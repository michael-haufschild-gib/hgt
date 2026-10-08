import GaloisForLFunctions.RHTower.WeilWorkQuantizationQChain
import GaloisForLFunctions.RHTower.WeilWorkQuantizationLaurentInverse
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Absolute pairings for canonical spectral q-chains

Two finite first moments justify the full arithmetic double-series interchange.
Every annihilator of a represented canonical phase must vanish at its q-decay
point. A zero-free exterior inverse cannot supply such an annihilator.
These are necessary constraints on a representation, not a construction of one.
-/

open Complex Set Filter MeasureTheory
open scoped ENNReal Topology ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
open GaloisForLFunctions.HTGeometry

theorem quantization_firstMoment_of_qWeight {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs) :
    Summable fun k => ‖p k‖ * (|(k : ℝ)| + 1) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow (n : ℕ) : (n : ℝ) + 1 ≤ (q : ℝ) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.mpr hq') (pow_nonneg (Nat.cast_nonneg q) n),
        Nat.cast_nonneg (α := ℝ) n]
  apply hp.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (by positivity))
  intro k
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hpow k.natAbs

theorem quantization_firstMoment_of_geometric {γ : ℕ → ℂ} {A R : ℝ}
    (hR : 1 < R) (hγ : ∀ n, ‖γ n‖ ≤ A / R ^ n) :
    Summable fun n => ‖γ n‖ * (n + 1) := by
  have hRi : ‖R⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact (inv_lt_one₀ (by linarith)).mpr hR
  have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 hRi
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hRi
  have hs : Summable fun n : ℕ => A * (((n : ℝ) + 1) * (R⁻¹) ^ n) := by
    simpa only [pow_one, pow_zero, one_mul, add_mul] using (h1.add h0).mul_left A
  apply hs.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (by positivity))
  intro n
  calc
    ‖γ n‖ * (n + 1) ≤ (A / R ^ n) * (n + 1) :=
      mul_le_mul_of_nonneg_right (hγ n) (by positivity)
    _ = A * ((n + 1) * (R⁻¹) ^ n) := by rw [inv_pow, div_eq_mul_inv]; ring

theorem quantization_summable_pairing {p : ℤ → ℂ} {γ b : ℕ → ℂ} {D : ℝ}
    (hD : 0 ≤ D) (hb : ∀ j, ‖b j‖ ≤ D * (j + 1))
    (hp : Summable fun k => ‖p k‖ * (|(k : ℝ)| + 1))
    (hγ : Summable fun l => ‖γ l‖ * (l + 1)) :
    Summable fun t : ℕ × ℕ => γ t.1 * p ((t.1 : ℤ) - t.2) * b t.2 := by
  let g : ℕ → ℝ := fun l => ‖γ l‖ * (l + 1)
  let h : ℤ → ℝ := fun k => ‖p k‖ * (|(k : ℝ)| + 1)
  have hg0 : ∀ l, 0 ≤ g l := fun l => mul_nonneg (norm_nonneg _) (by positivity)
  have hh0 : ∀ k, 0 ≤ h k := fun k => mul_nonneg (norm_nonneg _) (by positivity)
  have hs : Summable fun t : ℕ × ℤ => g t.1 * h t.2 := by
    apply (summable_prod_of_nonneg (fun t => mul_nonneg (hg0 t.1) (hh0 t.2))).mpr
    refine ⟨fun l => hp.mul_left (g l), ?_⟩
    simpa only [tsum_mul_left] using hγ.mul_right (∑' k, h k)
  have hi : Function.Injective (fun t : ℕ × ℕ => (t.1, (t.1 : ℤ) - t.2)) := by
    intro ⟨l, j⟩ ⟨l', j'⟩ he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    dsimp only at he1 he2
    have hj : j = j' := by omega
    exact Prod.ext he1 hj
  have ht := (hs.comp_injective hi).mul_left D
  apply Summable.of_norm
  apply ht.of_nonneg_of_le (fun t => norm_nonneg _)
  intro ⟨l, j⟩
  dsimp only [Function.comp_apply, g, h]
  simp only [norm_mul, Int.cast_sub, Int.cast_natCast]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hweight : (j : ℝ) + 1 ≤ (l + 1) * (|(l : ℝ) - j| + 1) := by
    nlinarith [neg_le_abs ((l : ℝ) - j), mul_nonneg hl0 (abs_nonneg ((l : ℝ) - j))]
  calc
    ‖γ l‖ * ‖p ((l : ℤ) - j)‖ * ‖b j‖ ≤
        ‖γ l‖ * ‖p ((l : ℤ) - j)‖ * (D * (j + 1)) :=
      mul_le_mul_of_nonneg_left (hb j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖γ l‖ * ‖p ((l : ℤ) - j)‖ * (D * ((l + 1) * (|(l : ℝ) - j| + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hweight hD)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (‖γ l‖ * (l + 1) * (‖p ((l : ℤ) - j)‖ * (|(l : ℝ) - j| + 1))) := by ring

theorem quantization_pairing_eq_zero {p : ℤ → ℂ} {γ b : ℕ → ℂ} {D : ℝ}
    (hD : 0 ≤ D) (hb : ∀ j, ‖b j‖ ≤ D * (j + 1))
    (hp : Summable fun k => ‖p k‖ * (|(k : ℝ)| + 1))
    (hγ : Summable fun l => ‖γ l‖ * (l + 1))
    (hann : ∀ j : ℕ, (∑' l : ℕ, γ l * p ((l : ℤ) - j)) = 0) :
    (∑' l : ℕ, γ l * ∑' j : ℕ, p ((l : ℤ) - j) * b j) = 0 := by
  have hs := quantization_summable_pairing hD hb hp hγ
  calc
    (∑' l : ℕ, γ l * ∑' j : ℕ, p ((l : ℤ) - j) * b j) =
        ∑' l : ℕ, ∑' j : ℕ, γ l * p ((l : ℤ) - j) * b j := by
      simp only [tsum_mul_left, mul_assoc]
    _ = ∑' j : ℕ, ∑' l : ℕ, γ l * p ((l : ℤ) - j) * b j := hs.tsum_comm.symm
    _ = 0 := by simp only [tsum_mul_right, hann, zero_mul, tsum_zero]

theorem quantization_geometric_pairing_obstruction {p : ℤ → ℂ} {γ b : ℕ → ℂ}
    {D : ℝ} {d ρ : ℂ} (hD : 0 ≤ D) (hb : ∀ j, ‖b j‖ ≤ D * (j + 1))
    (hp : Summable fun k => ‖p k‖ * (|(k : ℝ)| + 1))
    (hγ : Summable fun l => ‖γ l‖ * (l + 1)) (hd : d ≠ 0)
    (hrow : ∀ l : ℕ, (∑' j : ℕ, p ((l : ℤ) - j) * b j) = d * ρ ^ l)
    (hann : ∀ j : ℕ, (∑' l : ℕ, γ l * p ((l : ℤ) - j)) = 0) :
    (∑' l : ℕ, γ l * ρ ^ l) = 0 := by
  have he := quantization_pairing_eq_zero hD hb hp hγ hann
  have he' : d * (∑' l : ℕ, γ l * ρ ^ l) = 0 := by
    calc
      _ = ∑' l : ℕ, γ l * (d * ρ ^ l) := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro l
        ring
      _ = 0 := by simpa only [hrow] using he
  exact (mul_eq_zero.mp he').resolve_left hd

/-- Every summable coefficient annihilator of an actual q-chain vanishes at its decay point. -/
theorem quantization_phase_annihilator_vanishes {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I))
    {γ : ℕ → ℂ} (hγ : Summable fun l => ‖γ l‖ * (l + 1))
    (hann : ∀ j : ℕ, (∑' l : ℕ, γ l * p ((l : ℤ) - j)) = 0) :
    (∑' l : ℕ, γ l * (quantizationQDecay q : ℂ) ^ l) = 0 := by
  obtain ⟨D, hD, hb⟩ := exists_bound_quantizationQCoeff hW hq
  obtain ⟨d, hd, hrow⟩ := quantization_phase_qchain hW hq hp hphase
  exact quantization_geometric_pairing_obstruction hD.le hb
    (quantization_firstMoment_of_qWeight hq hp) hγ hd hrow hann

/-- The analytic exterior inverse cannot annihilate all columns of an actual q-chain. -/
theorem quantization_phase_exteriorInverse_not_annihilator
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I))
    {f : ℂ → ℂ} {r M R : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hf : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ M)
    (hR1 : 1 < R) (hR : R < r⁻¹) :
    ¬ ∀ j : ℕ, (∑' l : ℕ,
      outerCoeff (quantizationExteriorInverse f r) R l * p ((l : ℤ) - j)) = 0 := by
  obtain ⟨A, _, hcoef, hsum⟩ := quantizationExteriorInverse_coefficients
    hr hM hf (by linarith) hR
  intro hann
  have he := quantization_phase_annihilator_vanishes hW hq hp hphase
    (quantization_firstMoment_of_geometric hR1 hcoef) hann
  have hw : ‖(quantizationQDecay q : ℂ)‖ < R := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (quantizationQDecay_pos q)] using (quantizationQDecay_lt_one hq).trans hR1
  apply quantizationExteriorInverse_ne_zero f r (quantizationQDecay q)
  rw [← (hsum _ hw).tsum_eq]
  exact he

end RHTower.WeilSpectral
