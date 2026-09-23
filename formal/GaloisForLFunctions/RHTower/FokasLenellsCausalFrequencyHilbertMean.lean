import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyMeanSquare
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyShift
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedFrequencyMeans
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.InnerProductSpace.Basic
open Complex Set Filter Topology
noncomputable section
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section FiniteHilbertMeans
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def vectorPencil (s : Finset I) (c z : I → ℂ) (h : I → H) (n : ℕ) : H :=
  ∑ i ∈ s, (c i * z i ^ n) • h i

private theorem unit_cross_phase (z : I → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) (i j : I) :
    star (z i) * z j = 1 ↔ i = j := by
  have hui : z i * star (z i) = 1 := by
    simpa [hz i] using Complex.mul_conj' (z i)
  have hsi : star (z i) * z i = 1 := by
    simpa [hz i] using Complex.conj_mul' (z i)
  constructor
  · intro h
    apply hinj
    symm
    calc
      z j = 1 * z j := (one_mul _).symm
      _ = (z i * star (z i)) * z j := by rw [hui]
      _ = z i * (star (z i) * z j) := by rw [mul_assoc]
      _ = z i := by rw [h, mul_one]
  · rintro rfl
    exact hsi

private theorem vectorPencil_inner_mean [DecidableEq I] (s : Finset I)
    (c z : I → ℂ) (h : I → H) (hz : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective z) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N,
      inner ℂ (vectorPencil s c z h n) (vectorPencil s c z h n)) atTop
      (𝓝 (∑ i ∈ s, star (c i) * c i * inner ℂ (h i) (h i))) := by
  let pairs : Finset (I × I) := s ×ˢ s
  let C : I × I → ℂ := fun p => star (c p.1) * c p.2 * inner ℂ (h p.1) (h p.2)
  let W : I × I → ℂ := fun p => star (z p.1) * z p.2
  have hW : ∀ p ∈ pairs, ‖W p‖ = 1 := by
    intro p hp
    simp only [W, norm_mul, norm_star, hz, one_mul]
  have hl := RHTower.tendsto_finset_complex_geometric_cesaro pairs C W hW
  convert hl using 1
  · funext N
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    unfold vectorPencil
    rw [sum_inner]
    simp_rw [inner_sum]
    simp only [inner_smul_left, inner_smul_right, map_mul, map_pow]
    simp only [pairs, C, W, mul_pow, starRingEnd_apply]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · apply congrArg 𝓝
    symm
    dsimp only [pairs, C, W]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [if_pos ((unit_cross_phase z hz hinj i i).mpr rfl)]
    · intro j hj hji
      rw [if_neg]
      exact fun hp => hji ((unit_cross_phase z hz hinj i j).mp hp).symm
    · intro hi'
      exact (hi' hi).elim

private theorem hilbert_self_square (x : H) :
    inner ℂ x x = ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
  change inner ℂ x x = (‖x‖ : ℂ) ^ (2 : ℕ) at h
  exact h.trans (Complex.ofReal_pow ‖x‖ 2).symm

private theorem real_mean_inner (x : ℕ → H) (N : ℕ) :
    (((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, inner ℂ (x n) (x n)).re =
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖x n‖ ^ (2 : ℕ) := by
  have he : ((N : ℝ)⁻¹ : ℂ) * ∑ n ∈ Finset.range N, inner ℂ (x n) (x n) =
      (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖x n‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp only [hilbert_self_square, ← Complex.ofReal_sum]
    rw [Complex.ofReal_mul, Complex.ofReal_inv]
  rw [he, Complex.ofReal_re]

private theorem complex_star_square (z : ℂ) : star z * z = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  change (starRingEnd ℂ) z * z = _
  rw [Complex.conj_mul', Complex.ofReal_pow]

private theorem diagonal_real (s : Finset I) (c : I → ℂ) (h : I → H) :
    (∑ i ∈ s, star (c i) * c i * inner ℂ (h i) (h i)).re =
      ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) * ‖h i‖ ^ (2 : ℕ) := by
  have he : (∑ i ∈ s, star (c i) * c i * inner ℂ (h i) (h i)) =
      ((∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) * ‖h i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp only [complex_star_square, hilbert_self_square, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [he, Complex.ofReal_re]

private theorem vectorPencil_square_mean [DecidableEq I] (s : Finset I)
    (c z : I → ℂ) (h : I → H) (hz : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective z) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖vectorPencil s c z h n‖ ^ (2 : ℕ)) atTop (𝓝 (∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) * ‖h i‖ ^ (2 : ℕ))) := by
  have hc := vectorPencil_inner_mean s c z h hz hinj
  have hr := (Complex.continuous_re.tendsto _).comp hc
  simpa only [Function.comp_def, real_mean_inner, diagonal_real] using! hr
end FiniteHilbertMeans
section HilbertObservation
variable {E H I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem equiv_power_mode (T : E ≃ₗᵢ[ℂ] E) (v : I → E) (z : I → ℂ)
    (hT : ∀ i, T (v i) = z i • v i) (n : ℕ) (i : I) :
    (T ^ n) (v i) = z i ^ n • v i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change T ((T ^ n) (v i)) = _
    rw [ih, map_smul, hT, smul_smul, ← pow_succ]

private theorem observed_shift_packet (T : E ≃ₗᵢ[ℂ] E) (v : I → E) (z : I → ℂ)
    (hT : ∀ i, T (v i) = z i • v i) (J : E →L[ℂ] H)
    (s : Finset I) (c : I → ℂ) (n : ℕ) :
    J ((T ^ n) (∑ i ∈ s, c i • v i)) =
      vectorPencil s c z (fun i => J (v i)) n := by
  simp only [vectorPencil, map_sum, map_smul, equiv_power_mode T v z hT, smul_smul]

private theorem observed_shift_square_mean (T : E ≃ₗᵢ[ℂ] E) (v : I → E) (z : I → ℂ)
    (hT : ∀ i, T (v i) = z i • v i)
    (hz : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z)
    (J : E →L[ℂ] H) (s : Finset I) (c : I → ℂ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖J ((T ^ n) (∑ i ∈ s, c i • v i))‖ ^ (2 : ℕ)) atTop
      (𝓝 (∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) * ‖J (v i)‖ ^ (2 : ℕ))) := by
  classical
  have hm := vectorPencil_square_mean s c z (fun i => J (v i)) hz hinj
  simpa only [observed_shift_packet T v z hT] using hm
end HilbertObservation


/-- Every bounded Hilbert-valued observation has an exact mean-square law
along actual derivative-shift iterates of a finite mode packet. Distinct mode
characters remove all cross terms; each surviving weight is the observed
single-mode energy. -/
theorem causalFrequencyShift_hilbert_square_mean
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (s : Finset ℝ) (c : ℝ → ℂ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖J (((causalFrequencyShift b) ^ n)
        (∑ ω ∈ s, c ω • causalFrequencyMode b ω))‖ ^ (2 : ℕ)) atTop
      (𝓝 (∑ ω ∈ s, ‖c ω‖ ^ (2 : ℕ) * ‖J (causalFrequencyMode b ω)‖ ^ (2 : ℕ))) :=
  observed_shift_square_mean (causalFrequencyShift b) (causalFrequencyMode b)
    (fun ω => (causalUnitBoundaryRate b ω).val) (causalFrequencyShift_mode b)
    (norm_causalUnitBoundaryRate b) (causalUnitBoundaryRate_injective b) J s c

end RHTower.FokasLenells
