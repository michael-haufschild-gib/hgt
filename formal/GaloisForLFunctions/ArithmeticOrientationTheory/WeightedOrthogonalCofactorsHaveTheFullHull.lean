import GaloisForLFunctions.ArithmeticOrientationTheory.BoundedMultiplicativeSequencesActOnWienerAlgebras
import GaloisForLFunctions.ArithmeticOrientationTheory.TheOperatorHullOfAWienerAction
import GaloisForLFunctions.HTGeometry.BoundedKernelReindexing
import GaloisForLFunctions.HTGeometry.RealPositiveKernelComplexification
import GaloisForLFunctions.HTGeometry.AntipodalKernelExtension
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Weighted orthogonal cofactor modules

The diagonal kernels give cyclic modules with exact dilation norms and power
norms. Their Wiener actions are faithful at every weaker weight, so their
annihilator hull stays full even when their operator spectra contract.
All critical packet constraints and the unique antipodal extension persist.
-/

noncomputable section
set_option autoImplicit false

open Finset
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticOrientationTheory.WeightedWhiteNoise

/-- The exact norm of the cofactor at weight `σ`. -/
def amplitude (σ : ℝ) (j : ℕ+) : ℝ := (j : ℝ) ^ (-σ)

theorem amplitude_pos (σ : ℝ) (j : ℕ+) : 0 < amplitude σ j := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast j.property) _

theorem amplitude_one (σ : ℝ) : amplitude σ 1 = 1 := by simp [amplitude]

theorem amplitude_mul (σ : ℝ) (j k : ℕ+) :
    amplitude σ (j * k) = amplitude σ j * amplitude σ k := by
  simp only [amplitude, PNat.mul_coe, Nat.cast_mul]
  exact Real.mul_rpow (by positivity) (by positivity)

/-- Weighted orthogonal cofactor vectors. -/
def kernel (σ : ℝ) (j k : ℕ+) : ℝ := if j = k then amplitude σ j ^ 2 else 0

theorem kernel_self (σ : ℝ) (j : ℕ+) : kernel σ j j = amplitude σ j ^ 2 := if_pos rfl

theorem kernel_of_ne (σ : ℝ) {j k : ℕ+} (h : j ≠ k) : kernel σ j k = 0 := if_neg h

theorem kernel_symm (σ : ℝ) (j k : ℕ+) : kernel σ j k = kernel σ k j := by
  by_cases h : j = k
  · subst k
    rfl
  · rw [kernel_of_ne σ h, kernel_of_ne σ (Ne.symm h)]

theorem packet_energy (σ : ℝ) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel σ j k) =
      ∑ j ∈ S, c j ^ 2 * amplitude σ j ^ 2 := by
  apply sum_congr rfl
  intro j hj
  simp only [kernel, mul_ite, mul_zero]
  rw [sum_ite_eq, if_pos hj]
  ring

theorem packet_nonneg (σ : ℝ) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel σ j k := by
  rw [packet_energy]
  exact sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Exact mixed homogeneity holds for this whole family. -/
theorem kernel_dilation (σ : ℝ) (p j k : ℕ+) :
    kernel σ (p * j) (p * k) = amplitude σ p ^ 2 * kernel σ j k := by
  by_cases h : j = k
  · subst k
    rw [kernel_self, kernel_self, amplitude_mul, mul_pow]
  · have hpjk : p * j ≠ p * k := fun e => h (mul_left_cancel e)
    simp only [kernel, if_neg hpjk, if_neg h, mul_zero]

theorem packet_dilation (σ : ℝ) (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel σ (p * j) (p * k)) =
      amplitude σ p ^ 2 * (∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel σ j k) := by
  simp_rw [kernel_dilation]
  simp only [mul_sum]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

def complexKernel (σ : ℝ) (j k : ℕ+) : ℂ := kernel σ j k

instance (σ : ℝ) : Fact (IsPSDKernel (complexKernel σ)) :=
  ⟨isPSDKernel_of_real_packet_nonneg (kernel σ) (kernel_symm σ) (packet_nonneg σ)⟩

abbrev Hilbert (σ : ℝ) := KernelHilbert (complexKernel σ)

def vector (σ : ℝ) (j : ℕ+) : Hilbert σ := KernelHilbert.vector (complexKernel σ) j

theorem inner_vector (σ : ℝ) (j k : ℕ+) :
    ⟪vector σ k, vector σ j⟫_ℂ = (kernel σ j k : ℂ) := KernelHilbert.inner_vector j k

theorem norm_vector_sq (σ : ℝ) (j : ℕ+) : ‖vector σ j‖ ^ 2 = amplitude σ j ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_vector]
  change kernel σ j j = amplitude σ j ^ 2
  exact if_pos rfl

theorem norm_vector (σ : ℝ) (j : ℕ+) : ‖vector σ j‖ = amplitude σ j := by
  have h := norm_vector_sq σ j
  nlinarith only [h, norm_nonneg (vector σ j), (amplitude_pos σ j).le]

theorem complex_packet_dilation (σ : ℝ) (p : ℕ+) (c : ℕ+ →₀ ℂ) :
    (kernelForm (fun j k => complexKernel σ (p * j) (p * k)) c c).re ≤
      amplitude σ p ^ 2 * (kernelForm (complexKernel σ) c c).re :=
  kernelForm_real_re_le (fun S b => (packet_dilation σ p S b).le) c

/-- The exact weighted shift on the Gram completion. -/
def dilation (σ : ℝ) (p : ℕ+) : Hilbert σ →L[ℂ] Hilbert σ :=
  KernelHilbert.pushforward (complexKernel σ) (fun j => p * j)
    (amplitude_pos σ p).le (complex_packet_dilation σ p)

theorem dilation_vector (σ : ℝ) (p j : ℕ+) :
    dilation σ p (vector σ j) = vector σ (p * j) :=
  KernelHilbert.pushforward_vector _ _ _ _ j

/-- The upper contraction bound is attained on the cyclic receiver. -/
theorem norm_dilation (σ : ℝ) (p : ℕ+) : ‖dilation σ p‖ = amplitude σ p := by
  apply le_antisymm (KernelHilbert.norm_pushforward_le _ _ _ _)
  have h := (dilation σ p).le_opNorm (vector σ 1)
  have h1 : ‖vector σ 1‖ = 1 := by rw [norm_vector, amplitude_one]
  rw [dilation_vector, mul_one, h1, mul_one, norm_vector] at h
  exact h

theorem dilation_one (σ : ℝ) : dilation σ 1 = 1 := by
  apply KernelHilbert.ext_on_vectors (complexKernel σ)
  intro j
  change dilation σ 1 (vector σ j) = (1 : Hilbert σ →L[ℂ] Hilbert σ) (vector σ j)
  rw [dilation_vector, one_mul]
  rfl

theorem dilation_mul (σ : ℝ) (p q : ℕ+) :
    dilation σ p * dilation σ q = dilation σ (p * q) := by
  apply KernelHilbert.ext_on_vectors (complexKernel σ)
  intro j
  change dilation σ p (dilation σ q (vector σ j)) = dilation σ (p * q) (vector σ j)
  rw [dilation_vector, dilation_vector, dilation_vector, mul_assoc]

theorem receiver_cyclic (σ : ℝ) :
    Dense ((Submodule.span ℂ (Set.range (fun p => dilation σ p (vector σ 1))) :
      Submodule ℂ (Hilbert σ)) : Set (Hilbert σ)) := by
  simp only [dilation_vector, mul_one]
  exact KernelHilbert.dense_span_vectors (complexKernel σ)

open WienerAlgebraAt

def naturalDilation (σ : ℝ) (n : ℕ) : Hilbert σ →L[ℂ] Hilbert σ :=
  if hn : 0 < n then dilation σ ⟨n, hn⟩ else 0

theorem naturalDilation_zero (σ : ℝ) : naturalDilation σ 0 = 0 :=
  dif_neg (Nat.not_lt_zero 0)

theorem naturalDilation_pos (σ : ℝ) (n : ℕ) (hn : 0 < n) :
    naturalDilation σ n = dilation σ ⟨n, hn⟩ := dif_pos hn

theorem naturalDilation_one (σ : ℝ) : naturalDilation σ 1 = 1 := by
  rw [naturalDilation_pos σ 1 Nat.zero_lt_one]
  exact dilation_one σ

theorem naturalDilation_mul (σ : ℝ) (m n : ℕ) :
    naturalDilation σ (m * n) = naturalDilation σ m * naturalDilation σ n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_mul, naturalDilation_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mul_zero, naturalDilation_zero]
  rw [naturalDilation_pos σ m hm, naturalDilation_pos σ n hn,
    naturalDilation_pos σ (m * n) (Nat.mul_pos hm hn)]
  exact (dilation_mul σ ⟨m, hm⟩ ⟨n, hn⟩).symm

/-- Every weaker Wiener weight still integrates this action. -/
theorem norm_naturalDilation_le (σ τ : ℝ) (hτσ : τ ≤ σ) (n : ℕ) (hn : n ≠ 0) :
    ‖naturalDilation σ n‖ ≤ (n : ℝ) ^ (-τ) := by
  rw [naturalDilation_pos σ n (Nat.pos_of_ne_zero hn), norm_dilation]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    (neg_le_neg hτσ)

def representation (σ τ : ℝ) (hτσ : τ ≤ σ) :
    WienerAlgebraAt τ →ₐ[ℂ] (Hilbert σ →L[ℂ] Hilbert σ) :=
  sequenceRepresentation (naturalDilation σ) (naturalDilation_zero σ)
    (norm_naturalDilation_le σ τ hτσ) (naturalDilation_one σ) (naturalDilation_mul σ)

theorem representation_pointMass (σ τ : ℝ) (hτσ : τ ≤ σ) (n : ℕ) :
    representation σ τ hτσ (pointMass n) = naturalDilation σ n :=
  sequenceExtension_pointMass (naturalDilation σ) (naturalDilation_zero σ)
    (norm_naturalDilation_le σ τ hτσ) n

theorem norm_representation_pointMass (σ τ : ℝ) (hτσ : τ ≤ σ) (p : ℕ+) :
    ‖representation σ τ hτσ (pointMass p)‖ = amplitude σ p := by
  rw [representation_pointMass, naturalDilation_pos σ p p.property, norm_dilation]
  rfl

def coordinate (σ τ : ℝ) (hτσ : τ ≤ σ) (j : ℕ+) : WienerAlgebraAt τ →L[ℂ] ℂ :=
  (innerSL ℂ (vector σ j)).comp
    ((ContinuousLinearMap.apply ℂ (Hilbert σ) (vector σ 1)).comp
      (sequenceExtension (naturalDilation σ) (naturalDilation_zero σ)
        (norm_naturalDilation_le σ τ hτσ)))

theorem coordinate_pointMass (σ τ : ℝ) (hτσ : τ ≤ σ) (j : ℕ+) (n : ℕ) :
    coordinate σ τ hτσ j (pointMass n) =
      if n = (j : ℕ) then ((amplitude σ j ^ 2 : ℝ) : ℂ) else 0 := by
  change ⟪vector σ j, representation σ τ hτσ (pointMass n) (vector σ 1)⟫_ℂ = _
  rw [representation_pointMass]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (0 : ℕ) ≠ (j : ℕ) := Nat.ne_of_lt j.property
    rw [naturalDilation_zero]
    simp only [zero_apply, inner_zero_right, if_neg h0]
  · rw [naturalDilation_pos σ n hn, dilation_vector, mul_one, inner_vector]
    by_cases hnj : n = (j : ℕ)
    · have heq : (⟨n, hn⟩ : ℕ+) = j := Subtype.ext hnj
      rw [heq, if_pos hnj, kernel_self]
    · have heq : (⟨n, hn⟩ : ℕ+) ≠ j := fun h =>
        hnj (congrArg (fun q : ℕ+ => (q : ℕ)) h)
      rw [kernel_of_ne σ heq, Complex.ofReal_zero, if_neg hnj]

/-- Every coefficient is recovered by one Hilbert coordinate of the cyclic vector. -/
theorem coordinate_apply (σ τ : ℝ) (hτσ : τ ≤ σ) (j : ℕ+)
    (a : WienerAlgebraAt τ) :
    coordinate σ τ hτσ j a = a.toFn j * ((amplitude σ j ^ 2 : ℝ) : ℂ) := by
  have h := (coordinate σ τ hτσ j).hasSum (hasSum_pointMass a)
  simp only [map_smul] at h
  rw [← h.tsum_eq, tsum_eq_single (j : ℕ)]
  · rw [coordinate_pointMass, if_pos rfl, smul_eq_mul]
  · intro n hn
    rw [coordinate_pointMass, if_neg hn, smul_zero]

/-- Stronger contraction leaves the Wiener representation faithful. -/
theorem representation_injective (σ τ : ℝ) (hτσ : τ ≤ σ) :
    Function.Injective (representation σ τ hτσ) := by
  intro a b hab
  apply toFn_injective
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · let j : ℕ+ := ⟨n, hn⟩
    have heq : coordinate σ τ hτσ j a = coordinate σ τ hτσ j b := by
      change ⟪vector σ j, representation σ τ hτσ a (vector σ 1)⟫_ℂ =
        ⟪vector σ j, representation σ τ hτσ b (vector σ 1)⟫_ℂ
      rw [hab]
    rw [coordinate_apply, coordinate_apply] at heq
    have hw : ((amplitude σ j ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos (amplitude_pos σ j) 2).ne'
    exact mul_right_cancel₀ hw heq

def annihilator (σ τ : ℝ) (hτσ : τ ≤ σ) : Ideal (WienerAlgebraAt τ) :=
  RingHom.ker (representation σ τ hτσ).toRingHom

theorem annihilator_eq_bot (σ τ : ℝ) (hτσ : τ ≤ σ) : annihilator σ τ hτσ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro a ha
  change representation σ τ hτσ a = 0 at ha
  change a = 0
  exact representation_injective σ τ hτσ
    (ha.trans (map_zero (representation σ τ hτσ)).symm)

def hull (σ τ : ℝ) (hτσ : τ ≤ σ) : Set BohrPoint :=
  {ω | ∀ a ∈ annihilator σ τ hτσ, ArithmeticOrientationTheory.bohrEval τ a.toFn ω = 0}

/-- The annihilator hull is the full Bohr polydisk for every weight in the family. -/
theorem hull_eq_univ (σ τ : ℝ) (hτσ : τ ≤ σ) : hull σ τ hτσ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω a ha
  rw [annihilator_eq_bot] at ha
  have hz : a = 0 := ha
  subst a
  rw [← bohrCharacter_apply, map_zero]

/-- The canonical Bohr point with every positive coordinate equal to one. -/
def onePoint (τ : ℝ) : BohrPoint := halfPlanePoint τ (τ : ℂ) (by simp)

theorem onePoint_apply (τ : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (onePoint τ).ω n = 1 := by
  simp only [onePoint, halfPlanePoint, if_neg hn, sub_self, Complex.cpow_zero]

theorem norm_onePoint_pointMass (τ : ℝ) (p : ℕ+) :
    ‖ArithmeticOrientationTheory.bohrEval τ (pointMass (σ := τ) p).toFn (onePoint τ)‖ =
      (p : ℝ) ^ (-τ) := by
  have heval : ArithmeticOrientationTheory.bohrEval τ
      (pointMass (σ := τ) p).toFn (onePoint τ) =
        (onePoint τ).ω p / (p : ℂ) ^ (τ : ℂ) :=
    bohrEval_pointMass (σ := τ) (n := (p : ℕ)) p.property.ne' (onePoint τ)
  rw [heval, onePoint_apply τ p p.property.ne',
    norm_div, norm_one, norm_natCast_cpow p p.property.ne',
    Real.rpow_neg (by positivity), one_div]

/-- A hull character can exceed the represented norm even on a single cofactor. -/
theorem onePoint_exceeds_operator_norm (σ τ : ℝ) (hτσ : τ < σ) (p : ℕ+)
    (hp : 1 < (p : ℕ)) :
    ‖representation σ τ hτσ.le (pointMass p)‖ <
      ‖ArithmeticOrientationTheory.bohrEval τ (pointMass (σ := τ) p).toFn (onePoint τ)‖ := by
  rw [norm_representation_pointMass, norm_onePoint_pointMass]
  exact Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hp) (neg_lt_neg hτσ)

/-- The full annihilator hull is strictly larger than the norm-bounded character locus. -/
theorem onePoint_not_mem_operatorHull (σ τ : ℝ) (hτσ : τ < σ) :
    onePoint τ ∉ ArithmeticOrientationTheory.operatorHull (representation σ τ hτσ.le) := by
  intro h
  exact (not_lt_of_ge (h (pointMass (σ := τ) 2)))
    (onePoint_exceeds_operator_norm σ τ hτσ 2 (by norm_num))

end GaloisForLFunctions.ArithmeticOrientationTheory.WeightedWhiteNoise

namespace GaloisForLFunctions.ArithmeticOrientationTheory.WeightedWhiteNoise

open GaloisForLFunctions.HTGeometry

theorem kernel_one_one (σ : ℝ) : kernel σ 1 1 = 1 := by
  rw [kernel_self, amplitude_one, one_pow]

/-- Every weight above the critical exponent satisfies the critical cofactor radii. -/
theorem amplitude_le_critical (σ : ℝ) (hσ : 1 / 2 ≤ σ) (j : ℕ+) :
    amplitude σ j ≤ 1 / Real.sqrt (j : ℝ) := by
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.property
  calc
    _ ≤ (j : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hj (neg_le_neg hσ)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg (j : ℕ))]
      simp only [one_div]

theorem abs_kernel_le_critical_radius (σ : ℝ) (hσ : 1 / 2 ≤ σ) (j k : ℕ+) :
    |kernel σ j k| ≤ (1 / Real.sqrt (j : ℝ)) * (1 / Real.sqrt (k : ℝ)) := by
  by_cases hjk : j = k
  · subst k
    rw [kernel_self, abs_of_nonneg (sq_nonneg _), pow_two]
    exact mul_self_le_mul_self (amplitude_pos σ j).le (amplitude_le_critical σ hσ j)
  · rw [kernel_of_ne σ hjk, abs_zero]
    positivity

/-- The stronger homogeneous family also satisfies the source compactness packet bound. -/
theorem packet_critical_contraction (σ : ℝ) (hσ : 1 / 2 ≤ σ)
    (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel σ (p * j) (p * k)) ≤
      (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel σ j k) := by
  rw [packet_dilation]
  apply mul_le_mul_of_nonneg_right _ (packet_nonneg σ S c)
  calc
    amplitude σ p ^ 2 ≤ (1 / Real.sqrt (p : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (amplitude_pos σ p).le (amplitude_le_critical σ hσ p) 2
    _ = 1 / (p : ℝ) := by
      rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]

/-- Antipodal Gram data does not remove any member of the weighted family. -/
theorem existsUnique_antipodal_extension (σ : ℝ) :
    ∃! J : Option ℕ+ → Option ℕ+ → ℂ,
      IsPSDKernel J ∧ (∀ j k, J (some j) (some k) = complexKernel σ j k) ∧
        J none none = 1 ∧ J none (some 1) = -1 := by
  have h := existsUnique_antipodalKernelExtension
    (show IsPSDKernel (complexKernel σ) from Fact.out) (1 : ℕ+)
  have h1 : complexKernel σ 1 1 = 1 := by
    change (kernel σ 1 1 : ℂ) = 1
    rw [kernel_one_one, Complex.ofReal_one]
  simpa only [h1] using h

end GaloisForLFunctions.ArithmeticOrientationTheory.WeightedWhiteNoise

open Filter Topology

namespace GaloisForLFunctions.ArithmeticOrientationTheory.WeightedWhiteNoise

open WienerAlgebraAt

theorem amplitude_pow (σ : ℝ) (p : ℕ+) (n : ℕ) :
    amplitude σ (p ^ n) = amplitude σ p ^ n := by
  induction n with
  | zero => rw [pow_zero, amplitude_one, pow_zero]
  | succ n ih => rw [pow_succ, amplitude_mul, ih, pow_succ]

theorem dilation_pow (σ : ℝ) (p : ℕ+) (n : ℕ) :
    dilation σ p ^ n = dilation σ (p ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, dilation_one]
  | succ n ih => rw [pow_succ, ih, dilation_mul, pow_succ]

/-- The exact contraction persists through every power of a dilation. -/
theorem norm_dilation_pow (σ : ℝ) (p : ℕ+) (n : ℕ) :
    ‖dilation σ p ^ n‖ = amplitude σ p ^ n := by
  rw [dilation_pow, norm_dilation, amplitude_pow]

/-- Gelfand's formula recovers the strict dilation radius. -/
theorem spectralRadius_dilation (σ : ℝ) (p : ℕ+) :
    spectralRadius ℂ (dilation σ p) = ENNReal.ofReal (amplitude σ p) := by
  apply tendsto_nhds_unique (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius _)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [norm_dilation_pow, ← Real.rpow_natCast, ← Real.rpow_mul (amplitude_pos σ p).le,
    mul_one_div_cancel hnR, Real.rpow_one]

theorem norm_onePoint_pointMass_pow (τ : ℝ) (p : ℕ+) (n : ℕ) :
    ‖ArithmeticOrientationTheory.bohrEval τ
      (((pointMass (σ := τ) p) ^ n).toFn) (onePoint τ)‖ = amplitude τ p ^ n := by
  rw [← bohrCharacter_apply, map_pow, norm_pow, bohrCharacter_apply,
    norm_onePoint_pointMass]
  rfl

theorem norm_representation_pointMass_pow (σ τ : ℝ) (hτσ : τ ≤ σ) (p : ℕ+) (n : ℕ) :
    ‖representation σ τ hτσ ((pointMass p) ^ n)‖ = amplitude σ p ^ n := by
  rw [map_pow, representation_pointMass, naturalDilation_pos σ p p.property,
    norm_dilation_pow]
  rfl

/-- The extra hull character has no bound at all in the represented norm. -/
theorem onePoint_not_operator_norm_bounded (σ τ : ℝ) (hτσ : τ < σ) :
    ¬ ∃ C : ℝ, ∀ a : WienerAlgebraAt τ,
      ‖ArithmeticOrientationTheory.bohrEval τ a.toFn (onePoint τ)‖ ≤
        C * ‖representation σ τ hτσ.le a‖ := by
  rintro ⟨C, hC⟩
  let p : ℕ+ := 2
  have hp : 1 < (p : ℝ) := by norm_num [p]
  have hab : amplitude σ p < amplitude τ p :=
    Real.rpow_lt_rpow_of_exponent_lt hp (neg_lt_neg hτσ)
  have hratio : 1 < amplitude τ p / amplitude σ p :=
    (one_lt_div (amplitude_pos σ p)).mpr hab
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hratio
  have h := hC ((pointMass p) ^ n)
  rw [norm_onePoint_pointMass_pow, norm_representation_pointMass_pow] at h
  have hle : (amplitude τ p / amplitude σ p) ^ n ≤ C := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos (amplitude_pos σ p) n)).mpr h
  exact (not_lt_of_ge hle) hn

end GaloisForLFunctions.ArithmeticOrientationTheory.WeightedWhiteNoise
