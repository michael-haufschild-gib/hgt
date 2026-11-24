import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.VisibilityThreshold.Global
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BoundaryLoss.Multiplicity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting

/-! # Uniform overlap of finite heat waves detects the isometry boundary -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing

variable {ι : Type*} [Fintype ι]

/-- The finite heat wave with damping β and evolution time t. -/
def finiteHeatWave (a : ι → ℕ+) (β t : ℝ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => heat (thermalPoint β t) (a i))

def unitHeatWave (a : ι → ℕ+) (β t : ℝ) : EuclideanSpace ℂ ι :=
  ((‖finiteHeatWave a β t‖ : ℂ)⁻¹) • finiteHeatWave a β t

/-- Magnitude of the Hilbert overlap of the normalized waves at opposite times. -/
def finiteWaveOverlap (a : ι → ℕ+) (β t : ℝ) : ℝ :=
  ‖inner ℂ (finiteHeatWave a β (-t)) (finiteHeatWave a β t)‖ /
    (‖finiteHeatWave a β (-t)‖ * ‖finiteHeatWave a β t‖)

theorem overlap_as_unit_inner (a : ι → ℕ+) (β t : ℝ) :
    finiteWaveOverlap a β t = ‖inner ℂ (unitHeatWave a β (-t)) (unitHeatWave a β t)‖ := by
  simp only [finiteWaveOverlap,unitHeatWave,inner_smul_left,inner_smul_right,norm_mul,
    RCLike.norm_conj,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    div_eq_mul_inv,mul_inv_rev]
  ring

private theorem finiteWaveGram (a : ι → ℕ+) (β u v : ℝ) :
    inner ℂ (finiteHeatWave a β u) (finiteHeatWave a β v) =
      finiteHeatTrace a (thermalPoint (β+β) (v-u)) := by
  have he : (starRingEnd ℂ) (thermalPoint β u) + thermalPoint β v = thermalPoint (β+β) (v-u) := by
    apply Complex.ext <;> simp [sub_eq_add_neg,add_comm]
  change (∑ i, inner ℂ (heat (thermalPoint β u) (a i)) (heat (thermalPoint β v) (a i))) = _
  apply Finset.sum_congr rfl
  intro i _
  have hconj : (starRingEnd ℂ) (heat (thermalPoint β u) (a i)) = heat ((starRingEnd ℂ) (thermalPoint β u)) (a i) := by
    simp [heat,← Complex.exp_conj]
  rw [← he,heat_add,RCLike.inner_apply,hconj,mul_comm]

private theorem finiteWaveNorm (a : ι → ℕ+) (β t : ℝ) :
    ‖finiteHeatWave a β t‖^2 = ‖finiteHeatTrace a ((β+β:ℝ):ℂ)‖ := by
  have hn := congrArg norm (finiteWaveGram a β t t)
  rw [inner_self_eq_norm_sq_to_K,norm_pow] at hn
  change ‖((‖finiteHeatWave a β t‖:ℝ):ℂ)‖^2 = _ at hn
  rw [Complex.norm_of_nonneg (norm_nonneg _)] at hn
  simpa only [sub_self,thermalPoint,Complex.ofReal_zero,zero_mul,add_zero] using hn

theorem unitHeatWave_norm {κ : Type*} {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) (β t : ℝ) :
    ‖unitHeatWave a β t‖ = 1 := by
  have hpos := real_trace_norm_ge_one h (β+β)
  rw [← finiteWaveNorm a β t] at hpos
  have hne : ‖finiteHeatWave a β t‖ ≠ 0 := by
    intro hn
    rw [hn,sq,zero_mul] at hpos
    exact (not_le_of_gt zero_lt_one) hpos
  rw [unitHeatWave,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ hne]

theorem overlap_eq_visibility (a : ι → ℕ+) (β t : ℝ) :
    finiteWaveOverlap a β t = traceVisibility a (thermalPoint (β+β) (t+t)) := by
  have hn := (finiteWaveNorm a β (-t)).trans (finiteWaveNorm a β t).symm
  have he := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn
  rw [finiteWaveOverlap,finiteWaveGram,sub_neg_eq_add,he,← sq,finiteWaveNorm,traceVisibility,thermalPoint_re]

theorem overlap_at_zero {κ : Type*} {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) (β : ℝ) :
    finiteWaveOverlap a β 0 = 1 := by
  rw [overlap_eq_visibility,traceVisibility]
  simp only [thermalPoint_re]
  simp only [thermalPoint,add_zero,Complex.ofReal_zero,zero_mul]
  exact div_self (ne_of_gt (zero_lt_one.trans_le (real_trace_norm_ge_one h _)))

/-- All overlaps physically recorded on finite independent factors of the complete gas. -/
def finiteFactorOverlaps (β t : ℝ) : Set ℝ := {v | ∃ (A : Finset ℕ+) (B : Set ℕ+),
  exactLabelProduct (fun i : A => i.val) (fun j : B => j.val) ∧ v = finiteWaveOverlap (fun i : A => i.val) β t}

theorem finiteFactorOverlaps_eq (β t : ℝ) :
    finiteFactorOverlaps β t = allFiniteVisibilities (thermalPoint (β+β) (t+t)) := by
  ext v
  constructor
  · rintro ⟨A,B,h,rfl⟩
    rw [overlap_eq_visibility]
    exact ⟨_,visibility_mem _ h (spectrumPrimes_support _) _⟩
  · rintro ⟨_,A,B,h,_,rfl⟩
    exact ⟨A,B,h,(overlap_eq_visibility _ β t).symm⟩

/-- The exact lower endpoint, including its value throughout the physical Gibbs half-plane. -/
theorem finite_overlap_infimum {β t : ℝ} (hβ : 0 < β) (ht : t ≠ 0) :
    IsGLB (finiteFactorOverlaps β t)
      (if 1/2 < β then partitionVisibility (thermalPoint (β+β) (t+t)) else 0) := by
  rw [finiteFactorOverlaps_eq]
  split
  · rename_i h
    exact global_visibility_above_one (by rw [thermalPoint_re]; linarith)
  · rename_i h
    exact global_visibility_at_or_below_one (add_pos hβ hβ) (by linarith)
      (fun he => ht (by linarith))

/-- Existence of a positive overlap bound independent of the size and the spectrum of the extracted factor. -/
def uniformOverlap (β t : ℝ) := ∃ c : ℝ, 0 < c ∧ c ∈ lowerBounds (finiteFactorOverlaps β t)

theorem uniformOverlap_iff {β t : ℝ} (hβ : 0 < β) (ht : t ≠ 0) :
    uniformOverlap β t ↔ 1/2 < β := by
  have H := finite_overlap_infimum hβ ht
  constructor
  · rintro ⟨c,hc,hb⟩
    by_contra hn
    rw [if_neg hn] at H
    exact (not_le_of_gt hc) (H.2 hb)
  · intro h
    rw [if_pos h] at H
    refine ⟨_,?_,H.1⟩
    have h1 : 1 < β+β := by linarith
    exact div_pos (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using h1)))
      (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using h1)))

/-- A uniform finite-factor overlap witnesses square summability of the full heat wave. -/
theorem uniformOverlap_iff_full_wave {β t : ℝ} (hβ : 0 < β) (ht : t ≠ 0) :
    uniformOverlap β t ↔ Summable (fun n : ℕ+ => ‖heat (thermalPoint β t) n‖^2) := by
  rw [uniformOverlap_iff hβ ht,summable_heat_sq_iff,thermalPoint_re]

/-- Every finite measurement stays positive even at the threshold where their infimum vanishes. -/
theorem finite_overlap_pos {β t v : ℝ} (hβ : 0 < β) (hv : v ∈ finiteFactorOverlaps β t) : 0 < v := by
  rw [finiteFactorOverlaps_eq] at hv
  exact finite_visibility_pos (by simpa using add_pos hβ hβ) hv

/-- At or below the threshold there is a finite exact test below every prescribed tolerance. -/
theorem arbitrarily_small_overlap {β t : ℝ} (hβ : 0 < β) (hb : β ≤ 1/2) (ht : t ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) : ∃ v ∈ finiteFactorOverlaps β t, v < δ := by
  by_contra! h
  exact (not_lt_of_ge hb) ((uniformOverlap_iff hβ ht).mp ⟨δ,hδ,fun _ hv => h _ hv⟩)

/-- The boundary of uniform finite-factor visibility at any fixed nonzero time is precisely isometric composition. -/
theorem overlap_boundary_iff_isometric {β t : ℝ} (hβ : 0 < β) (ht : t ≠ 0) :
    (¬uniformOverlap β t ∧ ∀ ε : ℝ, 0 < ε → uniformOverlap (β+ε) t) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split (thermalPoint β t) f x := by
  rw [split_isometric_iff,thermalPoint_re,uniformOverlap_iff hβ ht]
  constructor
  · rintro ⟨hn,habove⟩
    apply le_antisymm (le_of_not_gt hn)
    by_contra! hlt
    let ε := (1/2-β)/2
    have hp : 0 < ε := by dsimp [ε]; linarith
    have hu := (uniformOverlap_iff (add_pos hβ hp) ht).mp (habove ε hp)
    dsimp [ε] at hu
    linarith
  · rintro rfl
    exact ⟨lt_irrefl _,fun ε hε => (uniformOverlap_iff (add_pos hβ hε) ht).mpr (lt_add_of_pos_right _ hε)⟩

#print axioms unitHeatWave_norm
#print axioms overlap_as_unit_inner
#print axioms overlap_at_zero
#print axioms arbitrarily_small_overlap
#print axioms overlap_eq_visibility
#print axioms finiteFactorOverlaps_eq
#print axioms finite_overlap_infimum
#print axioms uniformOverlap_iff
#print axioms uniformOverlap_iff_full_wave
#print axioms finite_overlap_pos
#print axioms overlap_boundary_iff_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
