import GaloisForLFunctions.RHTower.Deninger.DeningerHorizontalResidueTransverseGraphNoGo
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# No fixed Sobolev order controls residue evaluation across unbounded character rank

On a horizontal unitary torus of rank `d`, the character packet supported on the frequency cube
`{0,1}^d` and aligned at an evaluation point is an `L²`-unit vector whose evaluation there has
squared modulus `2^d`, while its Fourier--Sobolev energy of any fixed order `s` is at most
`(1 + d)^s`.  Exponential growth beats every polynomial weight, so no constant depending on `s`
alone bounds evaluation by the order-`s` Sobolev norm across all ranks.

* `deningerTorusAlignedPacket` : the aligned character packet on a frequency set, with unit `L²`
  mass and evaluation `√|S|` at the alignment point.
* `deningerCharacterSobolevEnergy`, `deningerTorusSobolevEnergy` : the Fourier--Sobolev energy of a
  trigonometric polynomial and of an `L²` class, agreeing on trigonometric polynomials, and equal
  to the genuine `L²` norm square at order zero.
* `deningerRankCubeWitness`, `deningerRankCubeWitness_prod` : the rank-cube witness and its product
  formula.
* `deningerRankCube_no_uniform_sobolev_bound` : the no-go.
-/

namespace RHTower

open MeasureTheory UnitAddTorus

noncomputable local instance deningerRankCubeMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance deningerRankCubeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance deningerRankCubeIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section AlignedPacket

variable {d : Type*} [Fintype d]

/-- Every torus character is unimodular at every point. -/
theorem deningerMFourier_norm_apply (k : d → ℤ) (zeta : UnitAddTorus d) :
    ‖mFourier k zeta‖ = 1 := by
  show ‖∏ i, fourier (k i) (zeta i)‖ = 1
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- Alignment coefficient of a character packet at an evaluation point. -/
noncomputable def deningerTorusAlignedCoeff (zeta : UnitAddTorus d) (k : d → ℤ) : ℂ :=
  (starRingEnd ℂ) (mFourier k zeta)

@[simp]
theorem deningerTorusAlignedCoeff_norm (zeta : UnitAddTorus d) (k : d → ℤ) :
    ‖deningerTorusAlignedCoeff zeta k‖ = 1 := by
  rw [deningerTorusAlignedCoeff, RCLike.norm_conj, deningerMFourier_norm_apply]

/-- The alignment coefficient cancels its own character value. -/
theorem deningerTorusAlignedCoeff_mul (zeta : UnitAddTorus d) (k : d → ℤ) :
    deningerTorusAlignedCoeff zeta k * mFourier k zeta = 1 := by
  rw [deningerTorusAlignedCoeff, RCLike.conj_mul, deningerMFourier_norm_apply]
  norm_num

/-- The aligned character kernel supported on a finite frequency set. -/
noncomputable def deningerTorusAlignedKernelLp (S : Finset (d → ℤ)) (zeta : UnitAddTorus d) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
  ∑ k ∈ S, deningerTorusAlignedCoeff zeta k • mFourierLp 2 k

/-- Orthonormality of the torus characters gives the aligned kernel the norm `√|S|`. -/
theorem deningerTorusAlignedKernelLp_norm (S : Finset (d → ℤ)) (zeta : UnitAddTorus d) :
    ‖deningerTorusAlignedKernelLp S zeta‖ = Real.sqrt S.card := by
  have hinner :
      (inner ℂ (deningerTorusAlignedKernelLp S zeta) (deningerTorusAlignedKernelLp S zeta)) =
        ((S.card : ℝ) : ℂ) := by
    rw [deningerTorusAlignedKernelLp,
      (orthonormal_mFourier (d := d)).inner_sum (deningerTorusAlignedCoeff zeta)
        (deningerTorusAlignedCoeff zeta)]
    have hone : ∀ k ∈ S,
        (starRingEnd ℂ) (deningerTorusAlignedCoeff zeta k) *
            deningerTorusAlignedCoeff zeta k = (1 : ℂ) := by
      intro k _
      rw [RCLike.conj_mul, deningerTorusAlignedCoeff_norm]
      norm_num
    rw [Finset.sum_congr rfl hone]
    simp
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner]
  simp

/-- The normalized aligned character packet, as a continuous function on the torus. -/
noncomputable def deningerTorusAlignedPacket (S : Finset (d → ℤ)) (zeta : UnitAddTorus d) :
    C(UnitAddTorus d, ℂ) :=
  ((Real.sqrt S.card : ℝ) : ℂ)⁻¹ • ∑ k ∈ S, deningerTorusAlignedCoeff zeta k • mFourier k

/-- Aligned evaluation: the packet takes the value `√|S|` at its alignment point. -/
theorem deningerTorusAlignedPacket_eval_self (S : Finset (d → ℤ)) (zeta : UnitAddTorus d) :
    deningerTorusAlignedPacket S zeta zeta = ((Real.sqrt S.card : ℝ) : ℂ) := by
  have hsum : (∑ k ∈ S, deningerTorusAlignedCoeff zeta k • mFourier k :
      C(UnitAddTorus d, ℂ)) zeta = ((S.card : ℝ) : ℂ) := by
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun k _ => deningerTorusAlignedCoeff_mul zeta k]
    simp
  rw [deningerTorusAlignedPacket, ContinuousMap.smul_apply, hsum, smul_eq_mul]
  rcases Finset.eq_empty_or_nonempty S with rfl | hS
  · simp
  · have hcard : 0 < S.card := Finset.card_pos.mpr hS
    have hpos : (0 : ℝ) < Real.sqrt S.card := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hcard)
    have hne : ((Real.sqrt S.card : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hsq : ((Real.sqrt S.card : ℝ) : ℂ) * ((Real.sqrt S.card : ℝ) : ℂ) =
        ((S.card : ℝ) : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ))
        (Real.mul_self_sqrt (Nat.cast_nonneg S.card))
    rw [← hsq, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The `L²` class of the packet is the normalized aligned kernel. -/
theorem deningerTorusAlignedPacket_toLp (S : Finset (d → ℤ)) (zeta : UnitAddTorus d) :
    ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus d)) ℂ
        (deningerTorusAlignedPacket S zeta) =
      ((Real.sqrt S.card : ℝ) : ℂ)⁻¹ • deningerTorusAlignedKernelLp S zeta := by
  rw [deningerTorusAlignedPacket, deningerTorusAlignedKernelLp, map_smul, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => map_smul _ _ _)

/-- Unit mass: a nonempty aligned packet is an `L²`-unit vector. -/
theorem deningerTorusAlignedPacket_norm_toLp {S : Finset (d → ℤ)} (hS : S.Nonempty)
    (zeta : UnitAddTorus d) :
    ‖ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus d)) ℂ
      (deningerTorusAlignedPacket S zeta)‖ = 1 := by
  have hpos : (0 : ℝ) < Real.sqrt S.card :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hS))
  rw [deningerTorusAlignedPacket_toLp, norm_smul, deningerTorusAlignedKernelLp_norm,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

end AlignedPacket

section SobolevEnergy

variable {d : Type*} [Fintype d]

/-- Euclidean square length of a character frequency. -/
def deningerFrequencyNormSq (k : d → ℤ) : ℝ :=
  ∑ i, ((k i : ℝ)) ^ 2

theorem deningerFrequencyNormSq_nonneg (k : d → ℤ) : 0 ≤ deningerFrequencyNormSq k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The Sobolev weight of a frequency is nonnegative. -/
theorem deningerSobolevWeight_nonneg (s : ℕ) (k : d → ℤ) :
    0 ≤ (1 + deningerFrequencyNormSq k) ^ s :=
  pow_nonneg (by linarith [deningerFrequencyNormSq_nonneg k]) s

/-- Fourier--Sobolev energy of order `s` of a trigonometric polynomial, given by its coefficients
on a finite frequency set. -/
noncomputable def deningerCharacterSobolevEnergy (s : ℕ) (S : Finset (d → ℤ))
    (c : (d → ℤ) → ℂ) : ℝ :=
  ∑ k ∈ S, (1 + deningerFrequencyNormSq k) ^ s * ‖c k‖ ^ 2

theorem deningerCharacterSobolevEnergy_nonneg (s : ℕ) (S : Finset (d → ℤ))
    (c : (d → ℤ) → ℂ) : 0 ≤ deningerCharacterSobolevEnergy s S c :=
  Finset.sum_nonneg fun k _ =>
    mul_nonneg (deningerSobolevWeight_nonneg s k) (sq_nonneg _)

/-- The Fourier coefficients of a trigonometric polynomial are its defining coefficients. -/
theorem deningerMFourierBasis_repr_sum (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ)
    (j : d → ℤ) :
    (mFourierBasis.repr (∑ k ∈ S, c k • mFourierLp 2 k)) j = if j ∈ S then c j else 0 := by
  rw [HilbertBasis.repr_apply_apply, coe_mFourierBasis]
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    exact (orthonormal_mFourier (d := d)).inner_right_sum c hj
  · rw [if_neg hj, inner_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hne : j ≠ k := by
      rintro rfl
      exact hj hk
    rw [inner_smul_right, (orthonormal_mFourier (d := d)).2 hne, mul_zero]

/-- **Parseval at order zero.**  The order-zero Fourier--Sobolev energy is the genuine `L²` norm
square, so the energy is not an arbitrary weight but the Fourier expression of a Hilbert norm. -/
theorem deningerCharacterSobolevEnergy_zero (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    deningerCharacterSobolevEnergy 0 S c = ‖∑ k ∈ S, c k • mFourierLp 2 k‖ ^ 2 := by
  have hinner : (inner ℂ (∑ k ∈ S, c k • mFourierLp (d := d) 2 k)
      (∑ k ∈ S, c k • mFourierLp 2 k)) = ((∑ k ∈ S, ‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [(orthonormal_mFourier (d := d)).inner_sum c c, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RCLike.conj_mul]
    norm_cast
  rw [deningerCharacterSobolevEnergy]
  simp only [pow_zero, one_mul]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (∑ k ∈ S, c k • mFourierLp (d := d) 2 k), hinner]
  simp [-Complex.ofReal_pow]

/-- Fourier--Sobolev energy of order `s` of an `L²` class. -/
noncomputable def deningerTorusSobolevEnergy (s : ℕ)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) : ENNReal :=
  ∑' k : d → ℤ, ENNReal.ofReal
    ((1 + deningerFrequencyNormSq k) ^ s * ‖(mFourierBasis.repr f) k‖ ^ 2)

/-- On a trigonometric polynomial the two energies agree. -/
theorem deningerTorusSobolevEnergy_sum (s : ℕ) (S : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    deningerTorusSobolevEnergy s (∑ k ∈ S, c k • mFourierLp 2 k) =
      ENNReal.ofReal (deningerCharacterSobolevEnergy s S c) := by
  rw [deningerTorusSobolevEnergy,
    tsum_eq_sum (s := S) fun j hj => by
      rw [deningerMFourierBasis_repr_sum, if_neg hj]
      simp]
  rw [deningerCharacterSobolevEnergy,
    ENNReal.ofReal_sum_of_nonneg fun k _ =>
      mul_nonneg (deningerSobolevWeight_nonneg s k) (sq_nonneg _)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [deningerMFourierBasis_repr_sum, if_pos hk]

end SobolevEnergy

section RankCube

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The `{0,1}`-frequency cube of a horizontal character lattice. -/
def deningerFrequencyCube (d : Type*) [Fintype d] [DecidableEq d] : Finset (d → ℤ) :=
  Fintype.piFinset fun _ => ({0, 1} : Finset ℤ)

theorem deningerFrequencyCube_card :
    (deningerFrequencyCube d).card = 2 ^ Fintype.card d := by
  rw [deningerFrequencyCube, Fintype.card_piFinset]
  simp [Finset.card_insert_of_notMem, Finset.prod_const]

theorem deningerFrequencyCube_nonempty : (deningerFrequencyCube d).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [deningerFrequencyCube, Fintype.mem_piFinset]
  intro i
  simp

theorem deningerFrequencyCube_mem_val {k : d → ℤ} (hk : k ∈ deningerFrequencyCube d) (i : d) :
    k i = 0 ∨ k i = 1 := by
  rw [deningerFrequencyCube, Fintype.mem_piFinset] at hk
  simpa using hk i

/-- Every cube frequency has square length at most the rank. -/
theorem deningerFrequencyCube_normSq_le {k : d → ℤ} (hk : k ∈ deningerFrequencyCube d) :
    deningerFrequencyNormSq k ≤ Fintype.card d := by
  rw [deningerFrequencyNormSq]
  calc ∑ i, ((k i : ℝ)) ^ 2 ≤ ∑ _i : d, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by
          rcases deningerFrequencyCube_mem_val hk i with h | h <;> rw [h] <;> norm_num
    _ = Fintype.card d := by simp

/-- The rank-cube witness: the aligned character packet on the `{0,1}` frequency cube. -/
noncomputable def deningerRankCubeWitness (zeta : UnitAddTorus d) : C(UnitAddTorus d, ℂ) :=
  deningerTorusAlignedPacket (deningerFrequencyCube d) zeta

/-- Fourier coefficients of the rank-cube witness. -/
noncomputable def deningerRankCubeCoeff (zeta : UnitAddTorus d) (k : d → ℤ) : ℂ :=
  ((Real.sqrt ((deningerFrequencyCube d).card : ℝ) : ℝ) : ℂ)⁻¹ *
    deningerTorusAlignedCoeff zeta k

/-- The witness is the trigonometric polynomial with those coefficients. -/
theorem deningerRankCubeWitness_toLp (zeta : UnitAddTorus d) :
    ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus d)) ℂ (deningerRankCubeWitness zeta) =
      ∑ k ∈ deningerFrequencyCube d, deningerRankCubeCoeff zeta k • mFourierLp 2 k := by
  rw [deningerRankCubeWitness, deningerTorusAlignedPacket_toLp, deningerTorusAlignedKernelLp,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [deningerRankCubeCoeff, smul_smul]

/-- **The product formula.**  The rank-cube witness is `2^{-d/2} ∏ⱼ (1 + conj(ζⱼ) zⱼ)`. -/
theorem deningerRankCubeWitness_prod (zeta z : UnitAddTorus d) :
    deningerRankCubeWitness zeta z =
      ((Real.sqrt ((deningerFrequencyCube d).card : ℝ) : ℝ) : ℂ)⁻¹ *
        ∏ i, (1 + (starRingEnd ℂ) (fourier 1 (zeta i)) * fourier 1 (z i)) := by
  have hfactor : ∀ i : d,
      (1 + (starRingEnd ℂ) (fourier 1 (zeta i)) * fourier 1 (z i)) =
        ∑ j ∈ ({0, 1} : Finset ℤ),
          (if j = 0 then (1 : ℂ)
            else (starRingEnd ℂ) (fourier 1 (zeta i)) * fourier 1 (z i)) := by
    intro i
    rw [show ({0, 1} : Finset ℤ) = {0, 1} from rfl]
    simp
  have hprod :
      ∏ i, (1 + (starRingEnd ℂ) (fourier 1 (zeta i)) * fourier 1 (z i)) =
        ∑ k ∈ deningerFrequencyCube d,
          ∏ i, (if k i = 0 then (1 : ℂ)
            else (starRingEnd ℂ) (fourier 1 (zeta i)) * fourier 1 (z i)) := by
    rw [Finset.prod_congr rfl fun i _ => hfactor i]
    exact Finset.prod_univ_sum _ _
  have hterm : ∀ k ∈ deningerFrequencyCube d,
      (∏ i, (if k i = 0 then (1 : ℂ)
        else (starRingEnd ℂ) (fourier 1 (zeta i)) * fourier 1 (z i))) =
        deningerTorusAlignedCoeff zeta k * mFourier k z := by
    intro k hk
    have hpoint : ∀ i : d,
        (if k i = 0 then (1 : ℂ)
          else (starRingEnd ℂ) (fourier 1 (zeta i)) * fourier 1 (z i)) =
          (starRingEnd ℂ) (fourier (k i) (zeta i)) * fourier (k i) (z i) := by
      intro i
      rcases deningerFrequencyCube_mem_val hk i with h | h
      · rw [h]
        simp
      · rw [h]
        simp
    rw [Finset.prod_congr rfl fun i _ => hpoint i, Finset.prod_mul_distrib,
      deningerTorusAlignedCoeff]
    congr 1
    · show (∏ i, (starRingEnd ℂ) (fourier (k i) (zeta i))) =
        (starRingEnd ℂ) (∏ i, fourier (k i) (zeta i))
      rw [map_prod]
  rw [deningerRankCubeWitness, deningerTorusAlignedPacket, ContinuousMap.smul_apply,
    smul_eq_mul, hprod, Finset.sum_congr rfl hterm]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]

/-- **Aligned evaluation.**  The witness has squared modulus `2^d` at the alignment point. -/
theorem deningerRankCubeWitness_eval_normSq (zeta : UnitAddTorus d) :
    ‖deningerRankCubeWitness zeta zeta‖ ^ 2 = 2 ^ Fintype.card d := by
  rw [deningerRankCubeWitness, deningerTorusAlignedPacket_eval_self, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Nat.cast_nonneg _), deningerFrequencyCube_card]
  push_cast
  ring

/-- **Unit mass.**  The witness is an `L²`-unit vector at every rank. -/
theorem deningerRankCubeWitness_norm_toLp (zeta : UnitAddTorus d) :
    ‖ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus d)) ℂ
      (deningerRankCubeWitness zeta)‖ = 1 :=
  deningerTorusAlignedPacket_norm_toLp deningerFrequencyCube_nonempty zeta

/-- **The Sobolev bound.**  The order-`s` energy of the witness is at most `(1 + d)^s`. -/
theorem deningerRankCubeWitness_sobolevEnergy_le (s : ℕ) (zeta : UnitAddTorus d) :
    deningerCharacterSobolevEnergy s (deningerFrequencyCube d) (deningerRankCubeCoeff zeta) ≤
      (1 + Fintype.card d : ℝ) ^ s := by
  have hcardpos : (0 : ℝ) < ((deningerFrequencyCube d).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr deningerFrequencyCube_nonempty)
  have hcoeff : ∀ k : d → ℤ,
      ‖deningerRankCubeCoeff zeta k‖ ^ 2 = ((deningerFrequencyCube d).card : ℝ)⁻¹ := by
    intro k
    rw [deningerRankCubeCoeff, norm_mul, deningerTorusAlignedCoeff_norm, mul_one, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt hcardpos.le]
  calc deningerCharacterSobolevEnergy s (deningerFrequencyCube d) (deningerRankCubeCoeff zeta)
      = ∑ k ∈ deningerFrequencyCube d,
          (1 + deningerFrequencyNormSq k) ^ s * ((deningerFrequencyCube d).card : ℝ)⁻¹ := by
        exact Finset.sum_congr rfl fun k _ => by rw [hcoeff]
    _ ≤ ∑ _k ∈ deningerFrequencyCube d,
          (1 + Fintype.card d : ℝ) ^ s * ((deningerFrequencyCube d).card : ℝ)⁻¹ := by
        refine Finset.sum_le_sum fun k hk => ?_
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact pow_le_pow_left₀ (by linarith [deningerFrequencyNormSq_nonneg k])
          (by linarith [deningerFrequencyCube_normSq_le hk]) s
    _ = (1 + Fintype.card d : ℝ) ^ s := by
        rw [Finset.sum_const, nsmul_eq_mul]
        field_simp

end RankCube

section NoGo

/-- **No rank-uniform fixed-order Sobolev bound.**  For every order `s` and every constant, some
rank produces a witness whose aligned evaluation exceeds the constant times its order-`s`
Fourier--Sobolev norm. -/
theorem deningerRankCube_no_uniform_sobolev_bound (s : ℕ) (C : ℝ) :
    ∃ (D : ℕ) (zeta : UnitAddTorus (Fin D)),
      C * Real.sqrt (deningerCharacterSobolevEnergy s (deningerFrequencyCube (Fin D))
          (deningerRankCubeCoeff zeta)) <
        ‖deningerRankCubeWitness zeta zeta‖ := by
  classical
  set C' : ℝ := max C 0 with hC'
  have hC'nonneg : 0 ≤ C' := le_max_right _ _
  obtain ⟨D, hD⟩ :
      ∃ D : ℕ, C' ^ 2 + 1 < deningerRankCubeSobolevEvaluationRatioSq s D := by
    have := (deningerRankCubeSobolevEvaluationRatioSq_tendsto_atTop s).eventually
      (Filter.eventually_gt_atTop (C' ^ 2 + 1))
    exact this.exists
  refine ⟨D, fun _ => 0, ?_⟩
  set zeta : UnitAddTorus (Fin D) := fun _ => 0 with hzeta
  have hcard : Fintype.card (Fin D) = D := Fintype.card_fin D
  have hpolypos : (0 : ℝ) < (1 + Fintype.card (Fin D) : ℝ) ^ s := by positivity
  have hbound := deningerRankCubeWitness_sobolevEnergy_le s zeta
  have hratio : C' ^ 2 * (1 + Fintype.card (Fin D) : ℝ) ^ s < 2 ^ Fintype.card (Fin D) := by
    rw [hcard]
    rw [deningerRankCubeSobolevEvaluationRatioSq] at hD
    have hden : (0 : ℝ) < ((D : ℝ) + 1) ^ s := by positivity
    have hlt : C' ^ 2 < (2 : ℝ) ^ D / ((D : ℝ) + 1) ^ s := by linarith
    calc C' ^ 2 * (1 + (D : ℝ)) ^ s = C' ^ 2 * ((D : ℝ) + 1) ^ s := by ring_nf
      _ < ((2 : ℝ) ^ D / ((D : ℝ) + 1) ^ s) * ((D : ℝ) + 1) ^ s :=
          mul_lt_mul_of_pos_right hlt hden
      _ = (2 : ℝ) ^ D := by field_simp
  have hsqrtle : Real.sqrt (deningerCharacterSobolevEnergy s (deningerFrequencyCube (Fin D))
      (deningerRankCubeCoeff zeta)) ≤ Real.sqrt ((1 + Fintype.card (Fin D) : ℝ) ^ s) :=
    Real.sqrt_le_sqrt hbound
  have hnorm : ‖deningerRankCubeWitness zeta zeta‖ =
      Real.sqrt ((2 : ℝ) ^ Fintype.card (Fin D)) := by
    have h := deningerRankCubeWitness_eval_normSq zeta
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hstep : C' * Real.sqrt ((1 + Fintype.card (Fin D) : ℝ) ^ s) <
      Real.sqrt ((2 : ℝ) ^ Fintype.card (Fin D)) := by
    have hlhs : C' * Real.sqrt ((1 + Fintype.card (Fin D) : ℝ) ^ s) =
        Real.sqrt (C' ^ 2 * (1 + Fintype.card (Fin D) : ℝ) ^ s) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC'nonneg]
    rw [hlhs]
    exact Real.sqrt_lt_sqrt (by positivity) hratio
  rw [hnorm]
  calc C * Real.sqrt (deningerCharacterSobolevEnergy s (deningerFrequencyCube (Fin D))
        (deningerRankCubeCoeff zeta))
      ≤ C' * Real.sqrt (deningerCharacterSobolevEnergy s (deningerFrequencyCube (Fin D))
        (deningerRankCubeCoeff zeta)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    _ ≤ C' * Real.sqrt ((1 + Fintype.card (Fin D) : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_left hsqrtle hC'nonneg
    _ < Real.sqrt ((2 : ℝ) ^ Fintype.card (Fin D)) := hstep

end NoGo

end RHTower
