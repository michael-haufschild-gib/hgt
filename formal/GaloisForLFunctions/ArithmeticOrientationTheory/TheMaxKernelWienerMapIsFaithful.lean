import GaloisForLFunctions.ArithmeticOrientationTheory.BoundedMultiplicativeSequencesActOnWienerAlgebras
import GaloisForLFunctions.HTGeometry.BoundedKernelReindexing

/-!
# The max-kernel Wiener map is faithful

Coordinate differences of max-kernel vectors recover finite coefficient
prefixes. Continuity passes this identity to the complete Wiener algebra,
so zero cyclic action forces every coefficient to vanish.
-/

section

noncomputable section
set_option autoImplicit false
open Finset
open scoped InnerProductSpace

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The max-kernel Gram recovers every Wiener coefficient from its cyclic vector. -/
theorem wiener_cyclic_map_injective_of_max_gram
    (ρ : WienerAlgebraAt (1 / 2) →ₐ[ℂ] (H →L[ℂ] H))
    (hρ : ∀ a, ‖ρ a‖ ≤ ‖a‖) (ξ : H)
    (hgram : ∀ j k : ℕ+,
      ⟪ρ (pointMass k) ξ, ρ (pointMass j) ξ⟫_ℂ =
        ((1 / ((max (j : ℕ) (k : ℕ) : ℕ) : ℝ) : ℝ) : ℂ)) :
    Function.Injective (fun a => ρ a ξ) := by
  let ρL : WienerAlgebraAt (1 / 2) →L[ℂ] (H →L[ℂ] H) :=
    ρ.toLinearMap.mkContinuous 1 (fun a => by
      change ‖ρ a‖ ≤ 1 * ‖a‖
      rw [one_mul]
      exact hρ a)
  let v (n : ℕ) : H := ρ (pointMass n) ξ
  let q (N : ℕ+) : WienerAlgebraAt (1 / 2) →L[ℂ] ℂ :=
    (innerSL ℂ (v N - v (N + 1))).comp ((ContinuousLinearMap.apply ℂ H ξ).comp ρL)
  let w (N : ℕ+) : ℝ := 1 / (N : ℝ) - 1 / ((N : ℝ) + 1)
  have hw (N : ℕ+) : 0 < w N := by
    apply sub_pos.mpr
    exact one_div_lt_one_div_of_lt (by exact_mod_cast N.property) (by linarith)
  have hpoint (N : ℕ+) (n : ℕ) :
      q N (pointMass n) = if n ∈ Icc 1 (N : ℕ) then (w N : ℂ) else 0 := by
    change ⟪v N - v (N + 1), v n⟫_ℂ = _
    rw [inner_sub_left]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hzero : (pointMass 0 : WienerAlgebraAt (1 / 2)) = 0 := by
        apply toFn_injective
        ext n
        simp only [toFn_pointMass, pointMassFn_apply, toFn_zero,
          ArithmeticFunction.zero_apply]
        split_ifs <;> simp_all
      have hv : v 0 = 0 := by simp only [v, hzero, map_zero, zero_apply]
      rw [hv]
      simp only [inner_zero_right, sub_zero, mem_Icc,
        show ¬ (1 : ℕ) ≤ 0 by omega, false_and, if_false]
    · let n' : ℕ+ := ⟨n, hn⟩
      let N' : ℕ+ := ⟨(N : ℕ) + 1, by omega⟩
      have h₁ : ⟪v N, v n⟫_ℂ = ((1 / ((max n (N : ℕ) : ℕ) : ℝ) : ℝ) : ℂ) :=
        hgram n' N
      have h₂ : ⟪v (N + 1), v n⟫_ℂ =
          ((1 / ((max n ((N : ℕ) + 1) : ℕ) : ℝ) : ℝ) : ℂ) := hgram n' N'
      rw [h₁, h₂]
      by_cases hnN : n ≤ (N : ℕ)
      · rw [if_pos (mem_Icc.mpr ⟨hn, hnN⟩), max_eq_right hnN,
          max_eq_right (hnN.trans (Nat.le_succ _))]
        simp only [w, Nat.cast_succ, Complex.ofReal_sub]
      · have hNn : (N : ℕ) + 1 ≤ n := by omega
        rw [if_neg (fun h => hnN (mem_Icc.mp h).2),
          max_eq_left (Nat.le_of_succ_le hNn), max_eq_left hNn, sub_self]
  have hcoord (N : ℕ+) (a : WienerAlgebraAt (1 / 2)) :
      q N a = (∑ n ∈ Icc 1 (N : ℕ), a.toFn n) * (w N : ℂ) := by
    have h := (q N).hasSum (hasSum_pointMass a)
    simp only [map_smul] at h
    rw [← h.tsum_eq, tsum_eq_sum (s := Icc 1 (N : ℕ))]
    · rw [sum_mul]
      exact sum_congr rfl fun n hn => by rw [hpoint, if_pos hn, smul_eq_mul]
    · intro n hn
      rw [hpoint, if_neg hn, smul_zero]
  have hzero (a : WienerAlgebraAt (1 / 2)) (ha : ρ a ξ = 0) : a = 0 := by
    apply toFn_injective
    ext n
    change a.toFn n = 0
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact a.toFn.map_zero
      · let N : ℕ+ := ⟨n, hn⟩
        have hq : q N a = 0 := by
          change ⟪v N - v (N + 1), ρ a ξ⟫_ℂ = 0
          rw [ha, inner_zero_right]
        rw [hcoord] at hq
        have hw' : (w N : ℂ) ≠ 0 := by exact_mod_cast (hw N).ne'
        have hs : (∑ m ∈ Icc 1 n, a.toFn m) = 0 :=
          (mul_eq_zero.mp hq).resolve_right hw'
        have hsingle : (∑ m ∈ Icc 1 n, a.toFn m) = a.toFn n := by
          apply sum_eq_single n
          · intro m hm hmn
            exact ih m (lt_of_le_of_ne (mem_Icc.mp hm).2 hmn)
          · intro hnot
            exact (hnot (mem_Icc.mpr ⟨hn, le_rfl⟩)).elim
        rwa [hsingle] at hs
  intro a b hab
  change ρ a ξ = ρ b ξ at hab
  have hdiff : ρ (a - b) ξ = 0 := by rw [map_sub, sub_apply, hab, sub_self]
  exact sub_eq_zero.mp (hzero (a - b) hdiff)

omit [CompleteSpace H] in
/-- A contractive Wiener action with the max-kernel cyclic Gram is faithful. -/
theorem wiener_representation_injective_of_max_gram
    (ρ : WienerAlgebraAt (1 / 2) →ₐ[ℂ] (H →L[ℂ] H))
    (hρ : ∀ a, ‖ρ a‖ ≤ ‖a‖) (ξ : H)
    (hgram : ∀ j k : ℕ+,
      ⟪ρ (pointMass k) ξ, ρ (pointMass j) ξ⟫_ℂ =
        ((1 / ((max (j : ℕ) (k : ℕ) : ℕ) : ℝ) : ℝ) : ℂ)) :
    Function.Injective ρ := by
  intro a b hab
  exact wiener_cyclic_map_injective_of_max_gram ρ hρ ξ hgram (congrArg (fun f => f ξ) hab)

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.wiener_cyclic_map_injective_of_max_gram
end
end
