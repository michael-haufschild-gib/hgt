import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.LogarithmicTorsionBound
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedProbeAtoms
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedTorsionCompactness
import GaloisForLFunctions.HTGeometry.RankOneHilbertSchmidt

/-!
# The full torsion form on logarithmic arithmetic probes

Normalized coordinates give the complete carrier of sequences with finite
logarithmic mass. The constructed bounded symmetric form retains the original
absolutely convergent arithmetic pair series. Its conductor-one prime row proves
the sharp necessary exponent for every bounded extension of the original matrix.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open HeightHomotopyArithmeticCounts ArithmeticIntersectionTheory

/-- Normalized Hilbert coordinates for logarithmically weighted arithmetic probes. -/
abbrev LogarithmicProbe := WeightedProbe 0

/-- The original arithmetic coefficients, undoing the logarithmic normalization. -/
def logProbeCoefficients (α : ℝ) (u : LogarithmicProbe) (n : ℕ) : ℝ :=
  probeCoefficients 0 u n/logProbeWeight α n

theorem logProbeCoefficients_weighted_square (α : ℝ) (u : LogarithmicProbe) (n : ℕ) :
    (logConductor n)^α*(logProbeCoefficients α u n)^2=(probeCoefficients 0 u n)^2 := by
  rw [logProbeCoefficients,←logProbeWeight_sq α n,div_pow]
  field_simp [(logProbeWeight_pos α n).ne']

/-- The logarithmic arithmetic mass is exactly the Hilbert norm, with no truncation loss. -/
theorem logProbeCoefficients_mass (α : ℝ) (u : LogarithmicProbe) :
    (∑' n : ℕ,(logConductor n)^α*(logProbeCoefficients α u n)^2)=‖u‖^2 := by
  simp_rw [logProbeCoefficients_weighted_square]
  simpa only [Real.rpow_zero,one_mul] using probeCoefficients_mass 0 u

theorem logProbeCoefficients_summable (α : ℝ) (u : LogarithmicProbe) :
    Summable (fun n : ℕ => (logConductor n)^α*(logProbeCoefficients α u n)^2) := by
  simp_rw [logProbeCoefficients_weighted_square]
  simpa only [Real.rpow_zero,one_mul] using probeCoefficients_summable 0 u

/-- Logarithmic arithmetic coefficients retain every Hilbert vector faithfully. -/
theorem logProbeCoefficients_injective (α : ℝ) : Function.Injective (logProbeCoefficients α) := by
  intro u v h
  apply probeCoefficients_injective 0
  funext n
  have he := congrFun h n
  simp only [logProbeCoefficients,div_eq_mul_inv] at he
  exact mul_right_cancel₀ (inv_ne_zero (logProbeWeight_pos α n).ne') he

/-- Every sequence of finite logarithmic mass is represented in the completed carrier. -/
theorem exists_logProbeCoefficients (α : ℝ) (x : ℕ → ℝ) (hx0 : x 0=0)
    (hx : Summable (fun n : ℕ => (logConductor n)^α*(x n)^2)) :
    ∃ u : LogarithmicProbe,logProbeCoefficients α u=x := by
  have hs : Summable (fun n : ℕ => (n:ℝ)^(0:ℝ)*(x n*logProbeWeight α n)^2) := by
    simp only [Real.rpow_zero,one_mul,mul_pow,logProbeWeight_sq]
    exact hx.congr (fun n => mul_comm _ _)
  obtain ⟨u,hu⟩ := exists_probeCoefficients 0 (fun n => x n*logProbeWeight α n)
    (by rw [hx0,zero_mul]) hs
  refine ⟨u,?_⟩
  funext n
  rw [logProbeCoefficients,hu,mul_div_cancel_right₀ _ (logProbeWeight_pos α n).ne']

/-- The original torsion kernel in normalized logarithmic coordinates. -/
def logarithmicTorsionKernel (α : ℝ) (m n : ℕ) : ℝ :=
  spacingLimitKernel m n/(logProbeWeight α m*logProbeWeight α n)

theorem logarithmicTorsionKernel_finite_bound (α : ℝ) (hα : 2 < α)
    (S : Finset ℕ) (x : ℕ → ℝ) (hS : ∀ n∈S,0 < n) :
    (∑ m∈S,∑ n∈S,|x m*x n*logarithmicTorsionKernel α m n|) ≤
      (logarithmicSchurCost (α-1)+1)*∑ n∈S,(n:ℝ)^(0:ℝ)*(x n)^2 := by
  have hb := spacingLimit_logarithmic_finite_bound α hα S (fun n => x n/logProbeWeight α n) hS
  have he (m n : ℕ) : (x m/logProbeWeight α m)*(x n/logProbeWeight α n)*spacingLimitKernel m n=
      x m*x n*logarithmicTorsionKernel α m n := by
    simp only [logarithmicTorsionKernel,div_eq_mul_inv,mul_inv_rev]
    ring
  have hw (n : ℕ) : (logConductor n)^α*(x n/logProbeWeight α n)^2=(x n)^2 := by
    rw [←logProbeWeight_sq α n,div_pow]
    field_simp [(logProbeWeight_pos α n).ne']
  simpa only [he,hw,Real.rpow_zero,one_mul] using hb

/-- The bounded logarithmic completion of the full arithmetic torsion form. -/
def logarithmicTorsionForm (α : ℝ) (hα : 2 < α) :
    LogarithmicProbe →L[ℝ] LogarithmicProbe →L[ℝ] ℝ :=
  weightedKernelContinuous 0 (logarithmicSchurCost (α-1)+1)
    (by linarith only [logarithmicSchurCost_pos (α-1)]) (logarithmicTorsionKernel α)
    (logarithmicTorsionKernel_finite_bound α hα)

/-- Normalization changes coordinates, preserving each original arithmetic summand. -/
theorem logarithmicTorsion_term (α : ℝ) (u v : LogarithmicProbe) (m n : ℕ) :
    probeCoefficients 0 u m*probeCoefficients 0 v n*logarithmicTorsionKernel α m n=
      logProbeCoefficients α u m*logProbeCoefficients α v n*spacingLimitKernel m n := by
  simp only [logProbeCoefficients,logarithmicTorsionKernel,div_eq_mul_inv,mul_inv_rev]
  ring

/-- The completed pairing is exactly the original arithmetic pair series. -/
theorem logarithmicTorsionForm_apply (α : ℝ) (hα : 2 < α) (u v : LogarithmicProbe) :
    logarithmicTorsionForm α hα u v=
      ∑' p : ℕ×ℕ,logProbeCoefficients α u p.1*logProbeCoefficients α v p.2*
        spacingLimitKernel p.1 p.2 := by
  change weightedKernelPairing 0 (logarithmicTorsionKernel α) u v=_
  unfold weightedKernelPairing
  exact tsum_congr (fun p => logarithmicTorsion_term α u v p.1 p.2)

/-- Every completed arithmetic pair series converges absolutely. -/
theorem logarithmicTorsionForm_absolute (α : ℝ) (hα : 2 < α) (u v : LogarithmicProbe) :
    Summable (fun p : ℕ×ℕ => |logProbeCoefficients α u p.1*logProbeCoefficients α v p.2*
      spacingLimitKernel p.1 p.2|) := by
  have hs := (weightedKernelPairing_absolute 0 (logarithmicSchurCost (α-1)+1)
    (by linarith only [logarithmicSchurCost_pos (α-1)]) (logarithmicTorsionKernel α)
    (logarithmicTorsionKernel_finite_bound α hα) u v).1
  exact hs.congr (fun p => congrArg abs (logarithmicTorsion_term α u v p.1 p.2))

theorem logarithmicTorsionForm_norm_le (α : ℝ) (hα : 2 < α) :
    ‖logarithmicTorsionForm α hα‖ ≤ 4*(logarithmicSchurCost (α-1)+1) :=
  weightedKernelContinuous_norm_le 0 _ _ _ _

theorem logarithmicTorsionForm_comm (α : ℝ) (hα : 2 < α) (u v : LogarithmicProbe) :
    logarithmicTorsionForm α hα u v=logarithmicTorsionForm α hα v u := by
  apply weightedKernelPairing_comm 0 (logarithmicTorsionKernel α) _ u v
  intro m n
  rw [logarithmicTorsionKernel,logarithmicTorsionKernel,spacingLimitKernel_comm,
    mul_comm (logProbeWeight α m)]

/-- The Hilbert operator representing the exact arithmetic torsion series. -/
def logarithmicTorsionOperator (α : ℝ) (hα : 2 < α) : LogarithmicProbe →L[ℝ] LogarithmicProbe :=
  HTGeometry.formRiesz (logarithmicTorsionForm α hα)

theorem logarithmicTorsionOperator_inner (α : ℝ) (hα : 2 < α) (u v : LogarithmicProbe) :
    inner ℝ (logarithmicTorsionOperator α hα u) v=
      ∑' p : ℕ×ℕ,logProbeCoefficients α u p.1*logProbeCoefficients α v p.2*
        spacingLimitKernel p.1 p.2 := by
  rw [logarithmicTorsionOperator,HTGeometry.inner_formRiesz,logarithmicTorsionForm_apply]

theorem logarithmicTorsionOperator_selfAdjoint (α : ℝ) (hα : 2 < α) :
    IsSelfAdjoint (logarithmicTorsionOperator α hα) :=
  HTGeometry.isSelfAdjoint_formRiesz (logarithmicTorsionForm_comm α hα)

/-- The normalized conductor basis reads precisely the original logarithmic matrix. -/
theorem logarithmicTorsionOperator_matrix (α : ℝ) (hα : 2 < α) (m n : ℕ) :
    inner ℝ (logarithmicTorsionOperator α hα (weightedProbeBasis 0 m)) (weightedProbeBasis 0 n)=
      logarithmicTorsionKernel α (m+1) (n+1) := by
  rw [logarithmicTorsionOperator,HTGeometry.inner_formRiesz]
  change weightedKernelPairing 0 (logarithmicTorsionKernel α) (weightedProbeBasis 0 m) (weightedProbeBasis 0 n)=_
  rw [weightedProbeBasis_apply,weightedProbeBasis_apply,weightedKernelPairing_normalizedAtoms]
  norm_num

/-- A bounded extension retaining the original normalized matrix exists exactly above exponent two. -/
theorem logarithmicTorsion_bounded_extension_iff (α : ℝ) :
    (∃ B : LogarithmicProbe →L[ℝ] LogarithmicProbe →L[ℝ] ℝ,
      ∀ m n : ℕ,B (weightedProbeBasis 0 m) (weightedProbeBasis 0 n)=
        logarithmicTorsionKernel α (m+1) (n+1)) ↔ 2 < α := by
  constructor
  · rintro ⟨B,hB⟩
    have hs := HTGeometry.summable_norm_apply_sq (weightedProbeBasis 0) (B (weightedProbeBasis 0 0))
    have hinj : Function.Injective (fun p : Nat.Primes => (p:ℕ)-1) := by
      intro p q h
      apply Subtype.ext
      have hp := p.property.pos
      have hq := q.property.pos
      omega
    have hp : Summable (fun p : Nat.Primes =>
        ‖B (weightedProbeBasis 0 0) (weightedProbeBasis 0 ((p:ℕ)-1))‖^2) :=
      hs.comp_injective (i := fun p : Nat.Primes => (p:ℕ)-1) hinj
    have hq1 : logProbeWeight α 1=1 := by
      simp only [logProbeWeight,logConductor,Nat.cast_one,Real.log_one,add_zero,Real.one_rpow]
    have hpay : Summable (fun p : Nat.Primes => (primeStarCoupling p)^2/(logConductor p)^α) := by
      apply hp.congr
      intro p
      rw [hB,show 0+1=1 from rfl,Nat.sub_add_cancel p.property.pos,
        logarithmicTorsionKernel,primeStar_kernel_one,hq1,one_mul,
        Real.norm_eq_abs,sq_abs,div_pow,neg_sq,logProbeWeight_sq]
    by_contra h
    have hα : α ≤ 2 := le_of_not_gt h
    have hb : ∀ᶠ p : Nat.Primes in Filter.cofinite,(logConductor p)^α ≤ 5*(Real.log p)^2 := by
      filter_upwards [primeStar_logConductor_diagonal_bound α 1 hα] with p hp
      norm_num only [abs_one,one_mul] at hp
      have hd := RenormalizedArithmeticPotentialTheory.tameDifferent_nonneg (p:ℕ)
      linarith only [hp,hd]
    exact not_summable_primeStar_of_log_square_bound (fun p => (logConductor p)^α)
      (fun p => Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (one_le_logConductor p)) α)
      5 hb hpay
  · intro hα
    refine ⟨logarithmicTorsionForm α hα,fun m n => ?_⟩
    simpa only [logarithmicTorsionOperator,HTGeometry.inner_formRiesz] using
      logarithmicTorsionOperator_matrix α hα m n

/-- The original normalized arithmetic matrix determines its bounded completion uniquely. -/
theorem logarithmicTorsionForm_unique (α : ℝ) (hα : 2 < α)
    (B : LogarithmicProbe →L[ℝ] LogarithmicProbe →L[ℝ] ℝ)
    (hB : ∀ m n : ℕ,B (weightedProbeBasis 0 m) (weightedProbeBasis 0 n)=
      logarithmicTorsionKernel α (m+1) (n+1)) :
    B=logarithmicTorsionForm α hα := by
  apply lp.ext_continuousLinearMap (by norm_num)
  intro m
  apply ContinuousLinearMap.ext_ring
  change B (lp.single 2 m (1:ℝ))=logarithmicTorsionForm α hα (lp.single 2 m (1:ℝ))
  apply lp.ext_continuousLinearMap (by norm_num)
  intro n
  apply ContinuousLinearMap.ext_ring
  change B (lp.single 2 m (1:ℝ)) (lp.single 2 n (1:ℝ))=
    logarithmicTorsionForm α hα (lp.single 2 m (1:ℝ)) (lp.single 2 n (1:ℝ))
  rw [←weightedProbeBasis_apply 0 m,←weightedProbeBasis_apply 0 n,hB]
  symm
  simpa only [logarithmicTorsionOperator,HTGeometry.inner_formRiesz] using
    logarithmicTorsionOperator_matrix α hα m n

/-- The same explicit diagonal compensates the completed arithmetic form on every logarithmic probe. -/
theorem logarithmicTorsionForm_compensated_nonneg (α : ℝ) (hα : 2 < α) (u : LogarithmicProbe) :
    0 ≤ logarithmicTorsionForm α hα u u+logarithmicSchurCost (α-1)*‖u‖^2 := by
  have hfinite (S : Finset ℕ) (x : ℕ → ℝ) (hS : ∀ n∈S,0 < n) :
      (∑ m∈S,∑ n∈S,|x m*x n*logarithmicPrimeKernel α m n|) ≤
        logarithmicSchurCost (α-1)*∑ n∈S,(n:ℝ)^(0:ℝ)*(x n)^2 := by
    have hb := weilPrimeKernel_logarithmic_finite_bound α hα S (fun n => x n/logProbeWeight α n) hS
    have he (m n : ℕ) : (x m/logProbeWeight α m)*(x n/logProbeWeight α n)*
        ArithmeticEffectivityTheory.weilPrimeKernel m n = x m*x n*logarithmicPrimeKernel α m n := by
      simp only [logarithmicPrimeKernel,div_eq_mul_inv,mul_inv_rev]
      ring
    have hw (n : ℕ) : (logConductor n)^α*(x n/logProbeWeight α n)^2=(x n)^2 := by
      rw [←logProbeWeight_sq α n,div_pow]
      field_simp [(logProbeWeight_pos α n).ne']
    simpa only [he,hw,Real.rpow_zero,one_mul] using hb
  have hp := kernel_infinite_absolute_of_finite_bound 0 (logarithmicSchurCost (α-1))
    (logarithmicSchurCost_pos (α-1)).le (logarithmicPrimeKernel α) hfinite
    (probeCoefficients 0 u) rfl (probeCoefficients_summable 0 u)
  have he (p : ℕ×ℕ) : probeCoefficients 0 u p.1*probeCoefficients 0 u p.2*
      logarithmicPrimeKernel α p.1 p.2 = logProbeCoefficients α u p.1*logProbeCoefficients α u p.2*
        ArithmeticEffectivityTheory.weilPrimeKernel p.1 p.2 := by
    simp only [logProbeCoefficients,logarithmicPrimeKernel,div_eq_mul_inv,mul_inv_rev]
    ring
  simp_rw [he] at hp
  rw [probeCoefficients_mass] at hp
  have hL := (logarithmicTorsionForm_absolute α hα u u).of_abs
  have hlo : -(∑' p : ℕ×ℕ,|logProbeCoefficients α u p.1*logProbeCoefficients α u p.2*
      ArithmeticEffectivityTheory.weilPrimeKernel p.1 p.2|) ≤ logarithmicTorsionForm α hα u u := by
    rw [logarithmicTorsionForm_apply,←tsum_neg]
    exact hp.1.neg.tsum_le_tsum
      (fun p => spacingLimit_quadratic_entry_lower (logProbeCoefficients α u) p.1 p.2) hL
  linarith only [hp.2,hlo]

#print axioms logarithmicTorsionForm_compensated_nonneg
#print axioms logarithmicTorsionForm_unique
#print axioms logarithmicTorsion_bounded_extension_iff
#print axioms logProbeCoefficients_mass
#print axioms logProbeCoefficients_injective
#print axioms exists_logProbeCoefficients
#print axioms logarithmicTorsionForm_absolute
#print axioms logarithmicTorsionForm_norm_le
#print axioms logarithmicTorsionOperator_inner
#print axioms logarithmicTorsionOperator_selfAdjoint
#print axioms logarithmicTorsionOperator_matrix
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
