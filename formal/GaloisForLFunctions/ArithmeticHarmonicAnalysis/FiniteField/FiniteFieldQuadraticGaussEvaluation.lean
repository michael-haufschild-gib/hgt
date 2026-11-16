import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldQuadraticTraceNorm
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldQuadraticTraceLine
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldTraceCharacters
import Mathlib.NumberTheory.GaussSum
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Gauss sums of characters trivial on the base field

A character killed by the base cardinality plus one is trivial on all
base-field units. Averaging its Gauss sum over base-field additive
shifts isolates the trace-zero line. Every nonzero point on that line
has the same character value, giving the Gauss sum exactly.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]
variable (hdegree : Module.finrank K L = 2)

include hdegree in
/-- A character killed by the base cardinality plus one is trivial on base-field units. -/
theorem finiteField_quadratic_base_character (χ : MulChar L ℂ)
    (hχ : χ ^ (Fintype.card K + 1) = 1) (a : Kˣ) :
    χ (algebraMap K L (a : K)) = 1 := by
  obtain ⟨b, hb⟩ := FiniteField.norm_surjective K L (a : K)
  have hb0 : b ≠ 0 := by
    intro hzero
    rw [hzero, Algebra.norm_zero] at hb
    exact a.ne_zero hb.symm
  have hpow : χ b ^ (Fintype.card K + 1) = 1 := by
    rw [← MulChar.pow_apply' χ (Nat.succ_ne_zero _), hχ,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hb0)]
  have hn : algebraMap K L (Algebra.norm K b) = b ^ (Fintype.card K + 1) := by
    rw [finiteField_quadratic_norm hdegree, Nat.card_eq_fintype_card, pow_succ, mul_comm]
  rw [← hb, hn, map_pow, hpow]

private def baseRestriction (χ : MulChar L ℂ) : MulChar K ℂ :=
  { χ.toMonoidHom.comp (algebraMap K L).toMonoidHom with
    map_nonunit' := by
      intro a ha
      have ha0 : a = 0 := by
        by_contra h
        exact ha (isUnit_iff_ne_zero.mpr h)
      subst a
      change χ (algebraMap K L 0) = 0
      rw [map_zero, χ.map_zero] }

omit [Fintype L] in
private theorem sum_base_character (χ : MulChar L ℂ)
    (hbase : ∀ a : Kˣ, χ (algebraMap K L (a : K)) = 1) :
    (∑ a : K, χ (algebraMap K L a)) = (Fintype.card K - 1 : ℕ) := by
  classical
  have hres : baseRestriction (K := K) χ = 1 := by
    apply MulChar.ext
    intro a
    change χ (algebraMap K L (a : K)) = (1 : MulChar K ℂ) (a : K)
    rw [hbase a, MulChar.one_apply_coe]
  change (∑ a : K, baseRestriction χ a) = _
  rw [hres, MulChar.sum_one_eq_card_units, ← Nat.card_eq_fintype_card (α := Kˣ),
    Nat.card_units, Nat.card_eq_fintype_card]

include hdegree in
private theorem sum_trace_zero_character (χ : MulChar L ℂ)
    (hbase : ∀ a : Kˣ, χ (algebraMap K L (a : K)) = 1)
    (θ : L) (hθ0 : θ ≠ 0) (hθ : Algebra.trace K L θ = 0) :
    (∑ x : L, if Algebra.trace K L x = 0 then χ x else 0) =
      χ θ * (Fintype.card K - 1 : ℕ) := by
  classical
  have hline : (∑ a : K, χ (θ * algebraMap K L a)) =
      ∑ x ∈ Finset.univ.filter (fun x : L => Algebra.trace K L x = 0), χ x := by
    apply Finset.sum_bij (fun a _ => θ * algebraMap K L a)
    · intro a _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (finiteField_quadratic_trace_zero_iff hdegree θ hθ0 hθ _).mpr ⟨a, rfl⟩
    · intro a _ b _ hab
      exact (algebraMap K L).injective (mul_left_cancel₀ hθ0 hab)
    · intro x hx
      obtain ⟨a, ha⟩ := (finiteField_quadratic_trace_zero_iff hdegree θ hθ0 hθ x).mp
        (Finset.mem_filter.mp hx).2
      exact ⟨a, Finset.mem_univ _, ha.symm⟩
    · intro a _
      rfl
  rw [← Finset.sum_filter, ← hline]
  simp_rw [map_mul]
  rw [← Finset.mul_sum, sum_base_character χ hbase]

include hdegree in
/-- A nontrivial character killed by `q+1` has Gauss sum `q χ(θ)` for every nonzero trace-zero `θ`. -/
theorem finiteField_quadratic_gauss_evaluation (χ : MulChar L ℂ)
    (hχ : χ ≠ 1) (horder : χ ^ (Fintype.card K + 1) = 1)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (θ : L) (hθ0 : θ ≠ 0) (hθ : Algebra.trace K L θ = 0) :
    gaussSum χ (finiteFieldTraceCharacter (L := L) ψ) = Fintype.card K * χ θ := by
  classical
  let Ψ : AddChar L ℂ := finiteFieldTraceCharacter ψ
  let G := gaussSum χ Ψ
  have hbase := finiteField_quadratic_base_character hdegree χ horder
  have hscalar (a : K) : gaussSum χ (Ψ.mulShift (algebraMap K L a)) =
      if a = 0 then 0 else G := by
    by_cases ha : a = 0
    · subst a
      rw [map_zero, AddChar.mulShift_zero, gaussSum_one_right hχ, if_pos rfl]
    · rw [if_neg ha]
      have h := gaussSum_mulShift χ Ψ
        (Units.map (algebraMap K L).toMonoidHom (Units.mk0 a ha))
      change χ (algebraMap K L a) * gaussSum χ (Ψ.mulShift (algebraMap K L a)) = G at h
      have hbasea : χ (algebraMap K L a) = 1 := hbase (Units.mk0 a ha)
      rw [hbasea, one_mul] at h
      exact h
  have hleft : (∑ a : K, gaussSum χ (Ψ.mulShift (algebraMap K L a))) =
      (Fintype.card K - 1 : ℕ) * G := by
    simp_rw [hscalar]
    have hterm (a : K) : (if a = 0 then 0 else G) = (1 : MulChar K ℂ) a * G := by
      by_cases ha : a = 0
      · subst a
        rw [if_pos rfl, MulChar.map_zero, zero_mul]
      · rw [if_neg ha, MulChar.one_apply (isUnit_iff_ne_zero.mpr ha), one_mul]
    simp_rw [hterm]
    rw [← Finset.sum_mul, MulChar.sum_one_eq_card_units,
      ← Nat.card_eq_fintype_card (α := Kˣ), Nat.card_units, Nat.card_eq_fintype_card]
  have hinner (x : L) : (∑ a : K, Ψ (algebraMap K L a * x)) =
      if Algebra.trace K L x = 0 then (Fintype.card K : ℂ) else 0 := by
    change (∑ a : K, ψ (Algebra.trace K L (algebraMap K L a * x))) = _
    simp_rw [← Algebra.smul_def, map_smul, smul_eq_mul]
    by_cases hx : Algebra.trace K L x = 0
    · rw [if_pos hx]
      simp only [hx, mul_zero, AddChar.map_zero_eq_one, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one]
    · rw [if_neg hx]
      have hnon := AddChar.IsPrimitive.of_ne_one hψ hx
      have hs := AddChar.sum_eq_zero_of_ne_one hnon
      simpa only [AddChar.mulShift_apply, mul_comm] using hs
  have hright : (∑ a : K, gaussSum χ (Ψ.mulShift (algebraMap K L a))) =
      (Fintype.card K : ℂ) * (χ θ * (Fintype.card K - 1 : ℕ)) := by
    change (∑ a : K, ∑ x : L, χ x * Ψ (algebraMap K L a * x)) = _
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hinner]
    calc
      (∑ x : L, χ x * (if Algebra.trace K L x = 0 then (Fintype.card K : ℂ) else 0)) =
          (Fintype.card K : ℂ) * ∑ x : L, if Algebra.trace K L x = 0 then χ x else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> simp only [mul_zero, zero_mul, mul_comm]
      _ = _ := by rw [sum_trace_zero_character hdegree χ hbase θ hθ0 hθ]
  have hcount : ((Fintype.card K - 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt (Fintype.one_lt_card (α := K)))
  change G = (Fintype.card K : ℂ) * χ θ
  apply mul_left_cancel₀ hcount
  calc
    ((Fintype.card K - 1 : ℕ) : ℂ) * G =
        ∑ a : K, gaussSum χ (Ψ.mulShift (algebraMap K L a)) := hleft.symm
    _ = (Fintype.card K : ℂ) * (χ θ * (Fintype.card K - 1 : ℕ)) := hright
    _ = ((Fintype.card K - 1 : ℕ) : ℂ) * ((Fintype.card K : ℂ) * χ θ) := by ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
