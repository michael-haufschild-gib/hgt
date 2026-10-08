import GaloisForLFunctions.RHTower.WeilWorkQuantizationPhaseCoupling
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardCoefficients

/-!
# Arithmetic q-chains of the canonical reflection phase

Critical source energy bounds rescaled q-power coefficients polynomially.
Every resonant periodic representation of the actual phase then forces a
convergent Toeplitz equation with a nonzero geometric right side.
No periodic representation is asserted to follow from Weil positivity.
-/

open Complex Set Filter MeasureTheory
open scoped ENNReal Topology ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
open WeilHerglotz HamburgerStability HamburgerTwisted PhaseLockRigidity IntegerMassRigidity
  GaloisForLFunctions.HTGeometry

def quantizationQDecay (q : ℕ) : ℝ := Real.exp (-Real.log q / 2)

def quantizationQCoeff (lam : ℕ → ℝ) (q j : ℕ) : ℂ :=
  (quantizationQDecay q : ℂ) ^ j * dirichletExp (lamLog lam) (q ^ j)

theorem quantizationQDecay_pos (q : ℕ) : 0 < quantizationQDecay q := Real.exp_pos _

theorem quantizationQDecay_lt_one {q : ℕ} (hq : 2 ≤ q) : quantizationQDecay q < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  linarith

theorem quantizationQDecay_sq {q : ℕ} (hq : 1 ≤ q) :
    quantizationQDecay q ^ 2 = (q : ℝ)⁻¹ := by
  unfold quantizationQDecay
  rw [pow_two, ← Real.exp_add]
  rw [show -Real.log (q : ℝ) / 2 + -Real.log q / 2 = -Real.log q by ring,
    Real.exp_neg, Real.exp_log (by exact_mod_cast (show 0 < q by omega))]

theorem norm_quantizationQCoeff_sq {lam : ℕ → ℝ} {q : ℕ} (hq : 1 ≤ q) (j : ℕ) :
    ‖quantizationQCoeff lam q j‖ ^ 2 =
      ‖dirichletExp (lamLog lam) (q ^ j)‖ ^ 2 / (q ^ j : ℕ) := by
  simp only [quantizationQCoeff, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (quantizationQDecay_pos q), mul_pow]
  rw [← pow_mul, mul_comm j 2, pow_mul, quantizationQDecay_sq hq]
  simp only [inv_pow, Nat.cast_pow, div_eq_mul_inv, mul_comm]

theorem exists_bound_quantizationQCoeff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {q : ℕ} (hq : 2 ≤ q) :
    ∃ D : ℝ, 0 < D ∧ ∀ j : ℕ, ‖quantizationQCoeff lam q j‖ ≤ D * (j + 1) := by
  obtain ⟨K, hK, hbound⟩ := WeilSingularArithmetic.exists_forwardCoeff_critical_energy_le hW
  have hcoef : logZetaCoeff (fun n => if 2 ≤ n then lam n else 0) = lamLog lam := by
    funext n
    simp only [logZetaCoeff, lamLog]
    split_ifs <;> simp
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  let D := K * (1 + Real.log q) + 1
  have hD : 1 ≤ D := by
    dsimp [D]
    have := mul_nonneg hK (show 0 ≤ 1 + Real.log q by linarith)
    linarith
  refine ⟨D, by linarith, fun j => ?_⟩
  have hqj : 1 ≤ q ^ j := Nat.one_le_pow j q (by omega)
  have hterm : ‖WeilSingularArithmetic.forwardCoeff lam (q ^ j)‖ ^ 2 / (q ^ j : ℕ) ≤
      ∑ n ∈ Finset.Icc 1 (q ^ j), ‖WeilSingularArithmetic.forwardCoeff lam n‖ ^ 2 / n :=
    Finset.single_le_sum (f := fun n : ℕ => ‖WeilSingularArithmetic.forwardCoeff lam n‖ ^ 2 / n)
      (fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (Finset.mem_Icc.mpr ⟨hqj, le_rfl⟩)
  have he := hterm.trans (hbound (q ^ j) hqj)
  simp only [WeilSingularArithmetic.forwardCoeff, hcoef, Nat.cast_pow, Real.log_pow] at he
  have hs := norm_quantizationQCoeff_sq (lam := lam) (by omega : 1 ≤ q) j
  simp only [Nat.cast_pow] at hs
  rw [← hs] at he
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have he' : ‖quantizationQCoeff lam q j‖ ^ 2 ≤ D * (j + 1) := by
    dsimp [D]
    nlinarith [mul_nonneg hK hlog]
  have hDj : 1 ≤ D * (j + 1) := by nlinarith
  have hx := norm_nonneg (quantizationQCoeff lam q j)
  nlinarith [sq_nonneg (‖quantizationQCoeff lam q j‖ - D * (j + 1))]


theorem quantization_qpower_resonance {q : ℕ} (hq : 2 ≤ q) (l j : ℕ) :
    quantizationFrequencyResonates (2 * ((l : ℤ) - j : ℤ) * Real.log q) (q ^ l) (q ^ j) := by
  refine ⟨Nat.one_le_pow j q (by omega), ?_⟩
  simp only [Nat.cast_pow, Real.log_pow, Int.cast_sub, Int.cast_natCast]
  ring

theorem quantization_qpower_residue_zero {lam : ℕ → ℝ} {q : ℕ} (hq : 2 ≤ q)
    {l : ℕ} {k : ℤ} (hk : (l : ℤ) < k) :
    quantizationFrequencyResidue lam (2 * k * Real.log q) (q ^ l) = 0 := by
  classical
  unfold quantizationFrequencyResidue
  split_ifs with h
  · exfalso
    obtain ⟨n, hn, he⟩ := h
    have hnlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hqlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    have hk' : (l : ℝ) < k := by exact_mod_cast hk
    simp only [Nat.cast_pow, Real.log_pow] at he
    nlinarith
  · rfl

theorem quantization_qpower_residue_scaled {lam : ℕ → ℝ} {q : ℕ} (hq : 2 ≤ q)
    (l j : ℕ) :
    (quantizationQDecay q : ℂ) ^ l *
        quantizationFrequencyResidue lam (2 * ((l : ℤ) - j : ℤ) * Real.log q) (q ^ l) =
      quantizationQCoeff lam q j := by
  rw [quantizationFrequencyResidue_eq (quantization_qpower_resonance hq l j)]
  have hr : quantizationQDecay q ^ l *
      Real.exp (2 * (((l : ℤ) - j : ℤ) : ℝ) * Real.log q / 4) = quantizationQDecay q ^ j := by
    unfold quantizationQDecay
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
  simp only [Complex.ofReal_mul, Complex.ofReal_pow] at hc
  rw [← mul_assoc, hc]
  rfl

theorem quantization_qpower_residue_sum {lam : ℕ → ℝ} {q : ℕ} (hq : 2 ≤ q)
    (p : ℤ → ℂ) (l : ℕ) :
    (quantizationQDecay q : ℂ) ^ l *
        (∑' k : ℤ, p k * quantizationFrequencyResidue lam (2 * k * Real.log q) (q ^ l)) =
      ∑' j : ℕ, p ((l : ℤ) - j) * quantizationQCoeff lam q j := by
  let f : ℤ → ℂ := fun k => p k *
    quantizationFrequencyResidue lam (2 * k * Real.log q) (q ^ l)
  let g : ℕ → ℤ := fun j => l - j
  have hg : Function.Injective g := by
    intro a b h
    dsimp [g] at h
    exact_mod_cast (sub_right_inj.mp h)
  have hs : Function.support f ⊆ Set.range g := by
    intro k hk
    have hkl : k ≤ l := by
      by_contra h
      have he := quantization_qpower_residue_zero (lam := lam) hq (lt_of_not_ge h)
      exact hk (by simp [f, he])
    refine ⟨(l - k).toNat, ?_⟩
    dsimp [g]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hkl)]
    ring
  rw [← hg.tsum_eq hs, ← tsum_mul_left]
  apply tsum_congr
  intro j
  change (quantizationQDecay q : ℂ) ^ l *
      (p ((l : ℤ) - j) * quantizationFrequencyResidue lam
        (2 * ((l : ℤ) - j : ℤ) * Real.log q) (q ^ l)) = _
  rw [mul_left_comm, quantization_qpower_residue_scaled hq]

/-- The prescribed q-moment is exactly the radial frequency majorant. -/
theorem quantization_qfrequency_weight {q : ℕ} (hq : 2 ≤ q) (k : ℤ) :
    Real.exp (|2 * (k : ℝ) * Real.log q| / 2) = (q : ℝ) ^ k.natAbs := by
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hk : (k.natAbs : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hlog]
  rw [show 2 * |(k : ℝ)| * Real.log q / 2 = (k.natAbs : ℝ) * Real.log q by rw [hk]; ring,
    Real.exp_nat_mul, Real.exp_log (by exact_mod_cast (show 0 < q by omega))]

/-- Every q-chain row converges in the actual source. -/
theorem summable_quantization_qchain {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs) (l : ℕ) :
    Summable fun j : ℕ => p ((l : ℤ) - j) * quantizationQCoeff lam q j := by
  have hp' : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log q| / 2) := by
    simpa only [quantization_qfrequency_weight hq] using hp
  have hs := summable_quantizationFrequencyResidue hW hp'
    (Nat.one_le_pow l q (by omega))
  have hg : Function.Injective (fun j : ℕ => (l : ℤ) - j) := by
    intro a b h
    exact_mod_cast (sub_right_inj.mp h)
  have ht := (hs.comp_injective hg).mul_left ((quantizationQDecay q : ℂ) ^ l)
  apply ht.congr
  intro j
  dsimp only [Function.comp_apply]
  rw [mul_left_comm, quantization_qpower_residue_scaled hq]

/-- The exact q-chain forced by a representation of the actual canonical phase. -/
theorem quantization_phase_qchain {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I)) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ l : ℕ,
      (∑' j : ℕ, p ((l : ℤ) - j) * quantizationQCoeff lam q j) =
        d * (quantizationQDecay q : ℂ) ^ l := by
  have hp' : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log q| / 2) := by
    simpa only [quantization_qfrequency_weight hq] using hp
  obtain ⟨hd, he⟩ := quantization_phase_resonance_constant hW hp' hphase
  refine ⟨_, hd, fun l => ?_⟩
  rw [← quantization_qpower_residue_sum hq p l,
    he (q ^ l) (Nat.one_le_pow l q (by omega)), mul_comm]


end RHTower.WeilSpectral
