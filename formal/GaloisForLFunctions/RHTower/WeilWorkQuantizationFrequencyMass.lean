import GaloisForLFunctions.RHTower.WeilWorkQuantizationDilationInverse

/-!
# Normalized frequency masses and the full residue convolution

The exponentially weighted frequency mass is bounded on every real scale.
Its arithmetic dilation sum recovers the actual real-height residue. This
keeps all frequencies and all resonant integer coefficients.
-/

open Complex Set
noncomputable section
namespace RHTower.WeilSpectral
open IntegerMassRigidity AbelianTwist GaloisForLFunctions.HTGeometry

def quantizationFrequencyMassTerm {ι : Type} (p : ι → ℂ) (ω : ι → ℝ)
    (x : ℝ) (j : ι) : ℂ := by
  classical
  exact if Real.exp (ω j / 2) = x then p j * (Real.exp (-(ω j / 2)) : ℂ) else 0

def quantizationFrequencyMass {ι : Type} (p : ι → ℂ) (ω : ι → ℝ) (x : ℝ) : ℂ :=
  ∑' j, quantizationFrequencyMassTerm p ω x j

theorem norm_quantizationFrequencyMassTerm_le {ι : Type} (p : ι → ℂ) (ω : ι → ℝ)
    (x : ℝ) (j : ι) :
    ‖quantizationFrequencyMassTerm p ω x j‖ ≤ ‖p j‖ * Real.exp (|ω j| / 2) := by
  classical
  unfold quantizationFrequencyMassTerm
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs (ω j)]
  · simp only [norm_zero]
    positivity

theorem summable_quantizationFrequencyMassTerm {ι : Type} {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) (x : ℝ) :
    Summable (quantizationFrequencyMassTerm p ω x) :=
  hp.of_norm_bounded (norm_quantizationFrequencyMassTerm_le p ω x)

theorem norm_quantizationFrequencyMass_le {ι : Type} {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) (x : ℝ) :
    ‖quantizationFrequencyMass p ω x‖ ≤ ∑' j, ‖p j‖ * Real.exp (|ω j| / 2) := by
  have hs := summable_quantizationFrequencyMassTerm hp x
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum (norm_quantizationFrequencyMassTerm_le p ω x) hp)

theorem quantization_real_frequency_resonance_iff {ω x : ℝ} (hx : 0 < x) (n : ℕ) :
    quantizationFrequencyResonates (ω - 2 * Real.log x) 1 n ↔
      Real.exp (ω / 2) = x / n := by
  constructor
  · rintro ⟨hn, he⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [Nat.cast_one, Real.log_one] at he
    have hl : ω / 2 = Real.log (x / n) := by
      rw [Real.log_div hx.ne' hnR.ne']
      linarith
    rw [hl, Real.exp_log (div_pos hx hnR)]
  · intro he
    have hn : n ≠ 0 := by
      intro hn
      simp only [hn, Nat.cast_zero, div_zero] at he
      exact (Real.exp_ne_zero _ ) he
    have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    refine ⟨Nat.one_le_iff_ne_zero.mpr hn, ?_⟩
    have hl := congrArg Real.log he
    rw [Real.log_exp, Real.log_div hx.ne' hnR.ne'] at hl
    rw [Nat.cast_one, Real.log_one]
    linarith

theorem quantization_linTwist_three_halves (ω : ℝ) :
    linTwist ω (((3 / 2 : ℝ) : ℂ)) = (Real.exp (-(ω / 2)) : ℂ) := by
  rw [linTwist, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem quantization_normalized_residue_term {lam : ℕ → ℝ} {ω x : ℝ} {n : ℕ}
    (hn : quantizationFrequencyResonates (ω - 2 * Real.log x) 1 n) :
    LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n *
        (Real.exp (-(ω / 2)) : ℂ) =
      (Real.exp (-Real.log x) : ℂ) *
        quantizationFrequencyResidue lam (ω - 2 * Real.log x) 1 := by
  have ht := quantization_twist_term_resonant (dirichletExp (lamLog lam))
    (m := 1) le_rfl hn.1 hn.2 (((3 / 2 : ℝ) : ℂ))
  rw [Nat.cast_one, Complex.one_cpow, mul_one,
    ← quantizationFrequencyResidue_eq hn, quantization_linTwist_three_halves] at ht
  rw [← ht, ← mul_assoc, mul_comm (Real.exp (-Real.log x) : ℂ), mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add]
  rw [show -Real.log x + -((ω - 2 * Real.log x) / 2) = -(ω / 2) by ring]

theorem quantization_tsum_frequencyMassTerm_residue {ι : Type} {lam : ℕ → ℝ}
    (p : ι → ℂ) (ω : ι → ℝ) {x : ℝ} (hx : 0 < x) (j : ι) :
    (∑' n : ℕ, LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n *
      quantizationFrequencyMassTerm p ω (x / n) j) =
      (Real.exp (-Real.log x) : ℂ) *
        (p j * quantizationFrequencyResidue lam (ω j - 2 * Real.log x) 1) := by
  classical
  by_cases hex : ∃ n, quantizationFrequencyResonates (ω j - 2 * Real.log x) 1 n
  · obtain ⟨n, hn⟩ := hex
    rw [tsum_eq_single n]
    · rw [quantizationFrequencyMassTerm,
        if_pos ((quantization_real_frequency_resonance_iff hx n).mp hn)]
      calc _ = p j * (LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n *
          (Real.exp (-(ω j / 2)) : ℂ)) := by ring
        _ = _ := by rw [quantization_normalized_residue_term hn]; ring
    · intro m hm
      have hnone : Real.exp (ω j / 2) ≠ x / m := by
        intro he
        exact hm (quantizationFrequencyResonates_unique
          ((quantization_real_frequency_resonance_iff hx m).mpr he) hn)
      simp [quantizationFrequencyMassTerm, hnone]
  · have hzero (n : ℕ) : quantizationFrequencyMassTerm p ω (x / n) j = 0 := by
      have he : Real.exp (ω j / 2) ≠ x / n := fun he =>
        hex ⟨n, (quantization_real_frequency_resonance_iff hx n).mpr he⟩
      simp [quantizationFrequencyMassTerm, he]
    simp [hzero, quantizationFrequencyResidue, hex]

theorem quantization_frequencyMass_dilation {ι : Type} {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n *
      quantizationFrequencyMass p ω (x / n)) =
      (Real.exp (-(3 * Real.log x / 2)) : ℂ) * quantizationRealFrequencySum lam p ω x := by
  let A := LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ))
  have ha : Summable fun n => ‖A n‖ := summable_quantization_forward_terms hW
  have hsum : Summable (fun q : ℕ × ι => A q.1 *
      quantizationFrequencyMassTerm p ω (x / q.1) q.2) := by
    apply (ha.mul_of_nonneg hp (fun _ => norm_nonneg _)
      (fun _ => by positivity)).of_norm_bounded
    intro q
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_quantizationFrequencyMassTerm_le p ω (x / q.1) q.2) (norm_nonneg _)
  have he : (∑' n, A n * quantizationFrequencyMass p ω (x / n)) =
      (Real.exp (-Real.log x) : ℂ) *
        ∑' j, p j * quantizationFrequencyResidue lam (ω j - 2 * Real.log x) 1 := by
    calc
      _ = ∑' n, ∑' j, A n * quantizationFrequencyMassTerm p ω (x / n) j := by
        apply tsum_congr
        intro n
        exact (tsum_mul_left).symm
      _ = ∑' j, ∑' n, A n * quantizationFrequencyMassTerm p ω (x / n) j :=
        hsum.tsum_comm.symm
      _ = ∑' j, (Real.exp (-Real.log x) : ℂ) *
          (p j * quantizationFrequencyResidue lam (ω j - 2 * Real.log x) 1) := by
        apply tsum_congr
        exact quantization_tsum_frequencyMassTerm_residue p ω hx
      _ = _ := tsum_mul_left
  change (∑' n, A n * quantizationFrequencyMass p ω (x / n)) = _
  rw [he, quantizationRealFrequencySum, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.exp_add,
    show -(3 * Real.log x / 2) + Real.log x / 2 = -Real.log x by ring]

/-- The actual reciprocal recovers every weighted frequency mass from the
complete real-height residues. All infinite resonances are retained. -/
theorem quantization_frequencyMass_inverse {ι : Type} {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) {x : ℝ} (hx : 0 < x) :
    quantizationFrequencyMass p ω x =
      ∑' n : ℕ, LSeries.term (quantizationInverseCoeff lam) (((3 / 2 : ℝ) : ℂ)) n *
        ((Real.exp (-(3 * Real.log (x / n) / 2)) : ℂ) *
          quantizationRealFrequencySum lam p ω (x / n)) := by
  rw [← quantization_actual_dilation_inverse hW (norm_quantizationFrequencyMass_le hp) x]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [quantization_frequencyMass_dilation hW hp
      (div_pos hx (by exact_mod_cast Nat.pos_of_ne_zero hn))]

end RHTower.WeilSpectral
