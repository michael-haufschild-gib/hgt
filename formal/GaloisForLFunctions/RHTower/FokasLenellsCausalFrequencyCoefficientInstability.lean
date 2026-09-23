import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyMeanSquare
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyCoefficient
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Archimedean.Real.Basic
open Complex Set
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section CoefficientInstability
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem subtype_packet_bound (D : Submodule ℂ E) (v : I → D)
    (hb : ∀ (s : Finset I) (c : I → ℂ),
      ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) ≤ ‖∑ i ∈ s, c i • (v i).val‖ ^ (2 : ℕ))
    (s : Finset I) (c : I → ℂ) :
    ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) ≤ ‖∑ i ∈ s, c i • v i‖ ^ (2 : ℕ) := by
  have he : (∑ i ∈ s, c i • v i).val = ∑ i ∈ s, c i • (v i).val := by
    change D.subtype (∑ i ∈ s, c i • v i) = _
    simp only [map_sum, map_smul]
    rfl
  have hn : ‖∑ i ∈ s, c i • v i‖ ^ (2 : ℕ) = ‖∑ i ∈ s, c i • (v i).val‖ ^ (2 : ℕ) :=
    congrArg (fun w : E => ‖w‖ ^ (2 : ℕ)) he
  exact hn.symm ▸ hb s c

private theorem bounded_coefficients_large_norm [DecidableEq I]
    (v : I → E) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (hb : ∀ (s : Finset I) (c : I → ℂ),
      ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) ≤ ‖∑ i ∈ s, c i • v i‖ ^ (2 : ℕ))
    (q : ℕ → I) (hq : Function.Injective q) (C : ℝ) :
    ∃ u : E, (∀ i, ‖a i u‖ ≤ 1) ∧ C < ‖u‖ := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (C ^ (2 : ℕ) + 1)
  let s : Finset I := (Finset.range N).image q
  let u : E := ∑ i ∈ s, v i
  have hc : s.card = N := by
    change ((Finset.range N).image q).card = N
    rw [Finset.card_image_of_injective _ hq, Finset.card_range]
  have hbound : (N : ℝ) ≤ ‖u‖ ^ (2 : ℕ) := by
    have h := hb s (fun _ => 1)
    simpa only [norm_one, one_pow, one_smul, Finset.sum_const, nsmul_eq_mul, mul_one, hc] using h
  have ha : ∀ i, a i u = if i ∈ s then 1 else 0 := by
    intro i
    simp only [u, map_sum, hd]
    simp
  refine ⟨u, ?_, ?_⟩
  · intro i
    rw [ha]
    split_ifs <;> simp
  · by_contra h
    have hle : ‖u‖ ≤ C := le_of_not_gt h
    have hsq : ‖u‖ ^ (2 : ℕ) ≤ C ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg u) ((norm_nonneg u).trans hle)).mpr hle
    linarith
end CoefficientInstability
/-- Uniformly bounded actual scalar amplitudes coexist with arbitrarily large
bounded-chain norms. Thus the largest amplitude cannot control reconstruction
norm, even though the full amplitude family uniquely determines each vector. -/
theorem causalFrequencyCoefficient_bounded_unbounded_norm (b C : ℝ) :
    ∃ u : causalFrequencySpace b,
      (∀ ω : ℝ, ‖causalFrequencyCoefficient b ω u‖ ≤ 1) ∧ C < ‖u‖ :=
  bounded_coefficients_large_norm (causalFrequencyMode b) (causalFrequencyCoefficient b)
    (causalFrequencyCoefficient_mode b)
    (subtype_packet_bound (causalFrequencySpace b) (causalFrequencyMode b)
      (causalFrequencyPacket_norm_sq_lower_bound b))
    (fun n : ℕ => (n : ℝ)) Nat.cast_injective C

end RHTower.FokasLenells
