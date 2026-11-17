import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.CostasDifferenceFibers
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact kernel and rank of diagonal incidence

For an additive automorphism L of a finite field, incidence with translates
of the diagonal `(L(t),t)` has Gram operator `q I + J - E - H`.
Its kernel consists exactly of mean-zero functions of the multiplicative
coordinate. Consequently its nullity is `q-2` and its rank is `q²-2q+2`.
The Gram operator and the loss pattern are independent of L.

The proof applies the diagonal divided-difference identity of Low–Schmidt,
arXiv:2611.20974, equation (2), to actual translation operators. Fiber sums
identify the Gram operator, and the counting inner product transfers its
kernel classification to incidence itself.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Costas
variable {F : Type*} [Field F] [Fintype F] (L : F ≃+ F)
local instance : DecidableEq F := Classical.decEq F
local instance : Fintype Fˣ := Fintype.ofFinite Fˣ

/-- Convolution by the exact diagonal difference multiplicities. -/
def correlation : Module.End ℂ (F → Fˣ → ℂ) where
  toFun f a b := ∑ c : F, ∑ d : Fˣ,
    (Nat.card (DifferenceFiber L (a - c) (b / d)) : ℂ) * f c d
  map_add' f g := by
    ext a b
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z f := by
    ext a b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      ← Finset.mul_sum, mul_left_comm]

private theorem correlation_coefficient (a c : F) (b d : Fˣ) :
    (Nat.card (DifferenceFiber L (a - c) (b / d)) : ℂ) =
      (Fintype.card F : ℂ) * (if a = c ∧ b = d then 1 else 0) + 1 -
        (if b = d then 1 else 0) - (if a = c then 1 else 0) := by
  classical
  have h := differenceFiber_groupRing_coeff L (a - c) (b / d)
  simp only [sub_eq_zero, div_eq_one, Nat.card_eq_fintype_card] at h
  exact_mod_cast h

/-- Difference convolution separates into the identity and the two coordinate averages. -/
theorem correlation_apply (f : F → Fˣ → ℂ) (a : F) (b : Fˣ) :
    correlation L f a b = (Fintype.card F : ℂ) * f a b + (∑ c, ∑ d, f c d) -
      (∑ c, f c b) - ∑ d, f a d := by
  classical
  change (∑ c : F, ∑ d : Fˣ, _ * f c d) = _
  simp_rw [correlation_coefficient, sub_mul, add_mul, one_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hboth : (∑ c : F, ∑ d : Fˣ,
      ((Fintype.card F : ℂ) * (if a = c ∧ b = d then 1 else 0)) * f c d) =
      (Fintype.card F : ℂ) * f a b := by
    simp only [ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp
  have hcol : (∑ c : F, ∑ d : Fˣ, (if b = d then (1 : ℂ) else 0) * f c d) =
      ∑ c : F, f c b := by simp
  have hrow : (∑ c : F, ∑ d : Fˣ, (if a = c then (1 : ℂ) else 0) * f c d) =
      ∑ d : Fˣ, f a d := by simp
  rw [hboth, hcol, hrow]

private theorem unit_card_cast : (Fintype.card Fˣ : ℂ) = (Fintype.card F : ℂ) - 1 := by
  have h := Nat.card_units F
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  exact_mod_cast (show (Fintype.card Fˣ : ℤ) = (Fintype.card F : ℤ) - 1 by
    rw [h, Nat.cast_sub hq]; rfl)

private theorem sum_first_correlation (f : F → Fˣ → ℂ) (b : Fˣ) :
    (∑ a : F, correlation L f a b) =
      ((Fintype.card F : ℂ) - 1) * (∑ c : F, ∑ d : Fˣ, f c d) := by
  simp only [correlation_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

private theorem sum_second_correlation (f : F → Fˣ → ℂ) (a : F) :
    (∑ b : Fˣ, correlation L f a b) =
      (∑ d : Fˣ, f a d) + ((Fintype.card F : ℂ) - 2) * (∑ c : F, ∑ d : Fˣ, f c d) := by
  simp only [correlation_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_comm (f := fun b c => f c b), unit_card_cast]
  ring

/-- The only lost functions are independent of the additive coordinate and have zero multiplicative average. -/
theorem correlation_eq_zero_iff (f : F → Fˣ → ℂ) :
    correlation L f = 0 ↔ ∃ g : Fˣ → ℂ, (∑ b, g b) = 0 ∧ ∀ a b, f a b = g b := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  have hu : (Fintype.card F : ℂ) - 1 ≠ 0 := by
    rw [← unit_card_cast]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  constructor
  · intro hf
    have ht : (∑ c : F, ∑ d : Fˣ, f c d) = 0 := by
      have h := sum_first_correlation L f 1
      rw [hf] at h
      simp only [Pi.zero_apply, Finset.sum_const_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hu
    have hr (a : F) : (∑ d : Fˣ, f a d) = 0 := by
      have h := sum_second_correlation L f a
      rw [hf, ht, mul_zero, add_zero] at h
      simpa only [Pi.zero_apply, Finset.sum_const_zero] using h.symm
    have he (a : F) (b : Fˣ) : (Fintype.card F : ℂ) * f a b = ∑ c : F, f c b := by
      have h := congrFun (congrFun hf a) b
      rw [correlation_apply, ht, hr, add_zero, sub_zero] at h
      exact sub_eq_zero.mp h
    refine ⟨f 0, hr 0, fun a b => ?_⟩
    exact mul_left_cancel₀ hq ((he a b).trans (he 0 b).symm)
  · rintro ⟨g, hg, hf⟩
    ext a b
    rw [correlation_apply]
    simp only [hf, hg, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, add_zero, sub_self, Pi.zero_apply]

/-- Multiplicative-coordinate sum, whose kernel parametrizes all invisible functions. -/
def multiplicativeSum : (Fˣ → ℂ) →ₗ[ℂ] ℂ where
  toFun g := ∑ b, g b
  map_add' f g := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' z f := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- Explicit coordinates on the complete correlation kernel. -/
def correlationKernelEquiv : LinearMap.ker (correlation L) ≃ₗ[ℂ]
    LinearMap.ker (multiplicativeSum (F := F)) where
  toFun f := ⟨f.val 0, by
    obtain ⟨g, hg, he⟩ := (correlation_eq_zero_iff L f.val).mp f.property
    change (∑ b, f.val 0 b) = 0
    simp only [he, hg]⟩
  invFun g := ⟨fun _ => g.val, (correlation_eq_zero_iff L _).mpr ⟨g.val, g.property, fun _ _ => rfl⟩⟩
  left_inv f := by
    apply Subtype.ext
    obtain ⟨g, _, he⟩ := (correlation_eq_zero_iff L f.val).mp f.property
    ext a b
    exact (he 0 b).trans (he a b).symm
  right_inv g := rfl
  map_add' f g := rfl
  map_smul' z f := rfl

private theorem multiplicativeSum_ne_zero : multiplicativeSum (F := F) ≠ 0 := by
  classical
  intro h
  have he := LinearMap.congr_fun h (Pi.single (1 : Fˣ) (1 : ℂ))
  simp [multiplicativeSum] at he

/-- The diagonal difference convolution loses exactly q−2 independent functions. -/
theorem correlation_nullity_add_two :
    Module.finrank ℂ (LinearMap.ker (correlation L)) + 2 = Fintype.card F := by
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero (multiplicativeSum_ne_zero (F := F))
  rw [← (correlationKernelEquiv L).finrank_eq] at hk
  simp only [Module.finrank_fintype_fun_eq_card] at hk
  have hu : Fintype.card Fˣ = Fintype.card F - 1 := by
    simpa only [Nat.card_eq_fintype_card] using Nat.card_units F
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  omega

/-- Exact rank, stated without truncated subtraction: rank + 2q = q² + 2. -/
theorem correlation_rank :
    Module.finrank ℂ (LinearMap.range (correlation L)) + 2 * Fintype.card F =
      Fintype.card F ^ 2 + 2 := by
  have hk := correlation_nullity_add_two L
  have hr := LinearMap.finrank_range_add_finrank_ker (correlation L)
  have hu : Fintype.card Fˣ = Fintype.card F - 1 := by
    simpa only [Nat.card_eq_fintype_card] using Nat.card_units F
  simp only [Module.finrank_pi_fintype, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hr
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  rw [hu] at hr
  have hprod := congrArg (fun n : ℕ => Fintype.card F * n) (Nat.sub_add_cancel hq)
  simp only [Nat.mul_add, Nat.mul_one] at hprod
  nlinarith only [hk, hr, hprod]

/-- Incidence with all translates of the additive/multiplicative diagonal. -/
def incidence : Module.End ℂ (F → Fˣ → ℂ) where
  toFun f a b := ∑ t : Fˣ, f (a - L (t : F)) (b / t)
  map_add' f g := by ext a b; simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' z f := by
    ext a b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- Reverse diagonal incidence, the adjoint with respect to counting measure. -/
def reverseIncidence : Module.End ℂ (F → Fˣ → ℂ) where
  toFun f a b := ∑ t : Fˣ, f (a + L (t : F)) (b * t)
  map_add' f g := by ext a b; simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' z f := by
    ext a b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

private theorem difference_weighted_sum (f : F → Fˣ → ℂ) :
    (∑ x : F, ∑ r : Fˣ, (Nat.card (DifferenceFiber L x r) : ℂ) * f x r) =
      ∑ t : Fˣ, ∑ s : Fˣ, f (L (t : F) - L (s : F)) (t / s) := by
  classical
  let d : (Fˣ × Fˣ) → F × Fˣ := fun st =>
    (L (st.1 : F) - L (st.2 : F), st.1 / st.2)
  have hc (z : F × Fˣ) :
      Nat.card (DifferenceFiber L z.1 z.2) = (Finset.univ.filter (fun st => d st = z)).card := by
    obtain ⟨x, r⟩ := z
    simp only [Nat.card_eq_fintype_card, DifferenceFiber, Fintype.card_subtype, d, Prod.mk.injEq]
  have h := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Fˣ × Fˣ))) (t := (Finset.univ : Finset (F × Fˣ)))
    (g := d) (fun _ _ => Finset.mem_univ _) (fun z => f z.1 z.2)
  simp only [Finset.sum_const, nsmul_eq_mul, ← hc] at h
  simpa only [Fintype.sum_prod_type, d] using h

private def differenceIndexEquiv (a : F) (b : Fˣ) : (F × Fˣ) ≃ (F × Fˣ) where
  toFun z := (a - z.1, b / z.2)
  invFun z := (a - z.1, b / z.2)
  left_inv z := by ext <;> simp only [sub_sub_cancel, div_div_cancel]
  right_inv z := by ext <;> simp only [sub_sub_cancel, div_div_cancel]

private theorem correlation_double_sum (f : F → Fˣ → ℂ) (a : F) (b : Fˣ) :
    correlation L f a b = ∑ t : Fˣ, ∑ s : Fˣ,
      f (a - (L (t : F) - L (s : F))) (b / (t / s)) := by
  rw [← difference_weighted_sum L (fun x r => f (a - x) (b / r))]
  change (∑ c : F, ∑ d : Fˣ,
    (Nat.card (DifferenceFiber L (a - c) (b / d)) : ℂ) * f c d) = _
  have he : (∑ z : F × Fˣ,
      (Nat.card (DifferenceFiber L (a - z.1) (b / z.2)) : ℂ) * f z.1 z.2) =
      ∑ z : F × Fˣ, (Nat.card (DifferenceFiber L z.1 z.2) : ℂ) *
        f (a - z.1) (b / z.2) := by
    apply Fintype.sum_equiv (differenceIndexEquiv (F := F) a b)
    intro z
    simp only [differenceIndexEquiv, Equiv.coe_fn_mk, sub_sub_cancel, div_div_cancel]
  simpa only [Fintype.sum_prod_type] using he

/-- The exact difference convolution is the actual incidence Gram operator. -/
theorem incidence_mul_reverse : incidence L * reverseIncidence L = correlation L := by
  apply LinearMap.ext
  intro f
  funext a b
  change _ = correlation L f a b
  rw [correlation_double_sum]
  change (∑ t : Fˣ, ∑ s : Fˣ, f ((a - L (t : F)) + L (s : F)) ((b / t) * s)) = _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  apply congrArg₂ f
  · abel
  · simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ac_rfl

/-- Forward and reverse incidence commute on the abelian translation group. -/
theorem reverse_mul_incidence : reverseIncidence L * incidence L = correlation L := by
  apply LinearMap.ext
  intro f
  funext a b
  change _ = correlation L f a b
  rw [correlation_double_sum]
  change (∑ s : Fˣ, ∑ t : Fˣ, f ((a + L (s : F)) - L (t : F)) ((b * s) / t)) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  apply congrArg₂ f
  · abel
  · simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ac_rfl

private def translationIndexEquiv (t : Fˣ) : (F × Fˣ) ≃ (F × Fˣ) where
  toFun z := (z.1 - L (t : F), z.2 / t)
  invFun z := (z.1 + L (t : F), z.2 * t)
  left_inv z := by ext <;> simp only [sub_add_cancel, div_mul_cancel]
  right_inv z := by ext <;> simp only [add_sub_cancel_right, mul_div_cancel_right]

/-- Reverse incidence is adjoint to incidence for the exact counting inner product. -/
theorem incidence_pairing (f g : F → Fˣ → ℂ) :
    (∑ a : F, ∑ b : Fˣ, (starRingEnd ℂ) (f a b) * incidence L g a b) =
      ∑ a : F, ∑ b : Fˣ, (starRingEnd ℂ) (reverseIncidence L f a b) * g a b := by
  have he : (∑ z : F × Fˣ, (starRingEnd ℂ) (f z.1 z.2) * incidence L g z.1 z.2) =
      ∑ z : F × Fˣ, (starRingEnd ℂ) (reverseIncidence L f z.1 z.2) * g z.1 z.2 := by
    change (∑ z : F × Fˣ, (starRingEnd ℂ) (f z.1 z.2) * ∑ t : Fˣ,
        g (z.1 - L (t : F)) (z.2 / t)) =
      ∑ z : F × Fˣ, (starRingEnd ℂ) (∑ t : Fˣ, f (z.1 + L (t : F)) (z.2 * t)) * g z.1 z.2
    simp only [Finset.mul_sum, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun (z : F × Fˣ) (t : Fˣ) =>
        (starRingEnd ℂ) (f z.1 z.2) * g (z.1 - L (t : F)) (z.2 / t)),
      Finset.sum_comm (f := fun (z : F × Fˣ) (t : Fˣ) =>
        (starRingEnd ℂ) (f (z.1 + L (t : F)) (z.2 * t)) * g z.1 z.2)]
    apply Finset.sum_congr rfl
    intro t _
    apply Fintype.sum_equiv (translationIndexEquiv L t)
    intro z
    simp only [translationIndexEquiv, Equiv.coe_fn_mk, sub_add_cancel, div_mul_cancel]
  simpa only [Fintype.sum_prod_type] using he

private theorem counting_norm_eq_zero (f : F → Fˣ → ℂ) :
    (∑ a : F, ∑ b : Fˣ, (starRingEnd ℂ) (f a b) * f a b) = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hn (z : ℂ) : (starRingEnd ℂ) z * z = (Complex.normSq z : ℂ) := by
      rw [mul_comm]
      exact Complex.mul_conj z
    simp_rw [hn] at h
    have hr : (∑ a : F, ∑ b : Fˣ, Complex.normSq (f a b)) = 0 := by
      apply Complex.ofReal_injective
      change Complex.ofRealHom (∑ a : F, ∑ b : Fˣ, Complex.normSq (f a b)) =
        Complex.ofRealHom 0
      simp only [map_sum, map_zero]
      exact h
    ext a b
    have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg (f a b)))).mp hr a (Finset.mem_univ a)
    have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ =>
      Complex.normSq_nonneg (f a b))).mp ha b (Finset.mem_univ b)
    exact Complex.normSq_eq_zero.mp hb
  · intro h
    rw [h]
    simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]

/-- Incidence loses exactly the functions already invisible to its Gram operator. -/
theorem incidence_kernel : LinearMap.ker (incidence L) = LinearMap.ker (correlation L) := by
  ext f
  change incidence L f = 0 ↔ correlation L f = 0
  constructor
  · intro hf
    have h := LinearMap.congr_fun (reverse_mul_incidence L) f
    change reverseIncidence L (incidence L f) = correlation L f at h
    rw [hf, map_zero] at h
    exact h.symm
  · intro hf
    have h := incidence_pairing L (incidence L f) f
    have he := LinearMap.congr_fun (reverse_mul_incidence L) f
    change reverseIncidence L (incidence L f) = correlation L f at he
    rw [he, hf] at h
    simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at h
    exact (counting_norm_eq_zero (incidence L f)).mp h

/-- The complete incidence kernel is a mean-zero function of the multiplicative coordinate. -/
theorem incidence_eq_zero_iff (f : F → Fˣ → ℂ) :
    incidence L f = 0 ↔ ∃ g : Fˣ → ℂ, (∑ b, g b) = 0 ∧ ∀ a b, f a b = g b := by
  change f ∈ LinearMap.ker (incidence L) ↔ _
  rw [incidence_kernel]
  exact correlation_eq_zero_iff L f

/-- The diagonal incidence operator has nullity exactly q−2. -/
theorem incidence_nullity_add_two :
    Module.finrank ℂ (LinearMap.ker (incidence L)) + 2 = Fintype.card F := by
  rw [incidence_kernel]
  exact correlation_nullity_add_two L

/-- Exact rank of the genuine diagonal incidence operator. -/
theorem incidence_rank :
    Module.finrank ℂ (LinearMap.range (incidence L)) + 2 * Fintype.card F =
      Fintype.card F ^ 2 + 2 := by
  have ha := LinearMap.finrank_range_add_finrank_ker (incidence L)
  have hc := LinearMap.finrank_range_add_finrank_ker (correlation L)
  rw [incidence_kernel] at ha
  have he := Nat.add_right_cancel (ha.trans hc.symm)
  rw [he]
  exact correlation_rank L

/-- Every additive diagonal model has exactly the same incidence Gram operator. -/
theorem incidence_gram_independent (M : F ≃+ F) :
    reverseIncidence L * incidence L = reverseIncidence M * incidence M := by
  rw [reverse_mul_incidence, reverse_mul_incidence]
  apply LinearMap.ext
  intro f
  funext a b
  rw [correlation_apply, correlation_apply]

#print axioms incidence_gram_independent
#print axioms incidence_nullity_add_two
#print axioms incidence_rank
#print axioms incidence_eq_zero_iff
#print axioms correlation_nullity_add_two
#print axioms correlation_rank

#print axioms incidence_mul_reverse
#print axioms reverse_mul_incidence
#print axioms incidence_pairing
#print axioms correlation_eq_zero_iff
#print axioms correlationKernelEquiv
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Costas
