import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Law

/-! # Weak Haar convergence from norm recovery of all finite occupation preparations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology ComplexConjugate

/-- Powers of a unit phase synthesize a finite occupation vector in the
Hilbert space of the measured phase law. -/
def synthesis (μ : ProbabilityMeasure Circle) := polynomialSynthesisL2 (μ : Measure Circle)

private def basis (i : ℕ) : ℕ →₀ ℂ := Finsupp.single i 1

private theorem basis_pair (μ : ProbabilityMeasure Circle) (i j : ℕ) :
    inner ℂ (synthesis μ (basis i)) (synthesis μ (basis j)) =
      circleMeasureMomentZ (μ : Measure Circle) ((i:ℤ)-j) := by
  simp only [synthesis,basis,polynomialSynthesisL2_single,one_smul,circleMonomialLp_inner_exact]

private theorem uniform_pair (i j : ℕ) :
    circleMeasureMomentZ (uniform : Measure Circle) ((i:ℤ)-j) =
      inner ℂ (finsuppCoefficientL2 (basis i)) (finsuppCoefficientL2 (basis j)) := by
  change circleMeasureMomentZ circleLebesgue _ = _
  rw [circleMeasureMomentZ,integral_circleLebesgue_coe_zpow]
  simp only [basis,finsuppCoefficientL2_single,lp.inner_single_left,RCLike.inner_apply]
  by_cases h : i=j
  · subst j; simp
  · simp [lp.single_apply,h]
    omega

private theorem expand {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : (ℕ →₀ ℂ) →ₗ[ℂ] E) (d : ℕ →₀ ℂ) : T d = ∑ n ∈ d.support, d n • T (basis n) := by
  calc
    T d = T (d.sum Finsupp.single) := congrArg T (Finsupp.sum_single d).symm
    _ = _ := by
      rw [Finsupp.sum,map_sum]
      apply sum_congr rfl
      intro n _
      rw [←map_smul,basis,Finsupp.smul_single,smul_eq_mul,mul_one]

private theorem finite_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : (ℕ →₀ ℂ) →ₗ[ℂ] E) (u v : ℕ →₀ ℂ) :
    inner ℂ (T u) (T v) = ∑ i ∈ u.support, ∑ j ∈ v.support,
      (conj (u i)*v j)*inner ℂ (T (basis i)) (T (basis j)) := by
  rw [expand T u,expand T v,sum_inner]
  apply sum_congr rfl
  intro i _
  rw [inner_sum]
  apply sum_congr rfl
  intro j _
  rw [inner_smul_left,inner_smul_right,mul_assoc]

private def polar (Q : (ℕ →₀ ℂ) → ℝ) (u v : ℕ →₀ ℂ) : ℂ :=
  ((Q (u+v):ℂ) - Q (u-v) + ((Q (u-Complex.I • v):ℂ) - Q (u+Complex.I • v))*Complex.I)/4

private theorem polar_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : (ℕ →₀ ℂ) →ₗ[ℂ] E) (u v : ℕ →₀ ℂ) :
    inner ℂ (T u) (T v) = polar (fun d => ‖T d‖^2) u v := by
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ)]
  simp only [polar,map_add,map_sub,map_smul,Complex.ofReal_pow]
  rfl

private theorem pair_of_norms (μ : ℕ → ProbabilityMeasure Circle)
    (h : ∀ d, Tendsto (fun N => ‖synthesis (μ N) d‖^2) atTop (𝓝 (‖finsuppCoefficientL2 d‖^2)))
    (u v : ℕ →₀ ℂ) : Tendsto (fun N => inner ℂ (synthesis (μ N) u) (synthesis (μ N) v))
      atTop (𝓝 (inner ℂ (finsuppCoefficientL2 u) (finsuppCoefficientL2 v))) := by
  have C (d : ℕ →₀ ℂ) := Complex.continuous_ofReal.continuousAt.tendsto.comp (h d)
  have lim := (((C (u+v)).sub (C (u-v))).add
    (((C (u-Complex.I • v)).sub (C (u+Complex.I • v))).mul_const Complex.I)).div_const (4:ℂ)
  simpa only [polar_pair,polar,Function.comp_def] using lim

/-- The weak phase law is Haar exactly when every finite superposition
of occupations recovers its coefficient Hilbert norm in mean square. -/
theorem haar_iff_occupation_norms (μ : ℕ → ProbabilityMeasure Circle) :
    Tendsto μ atTop (𝓝 uniform) ↔ ∀ d : ℕ →₀ ℂ,
      Tendsto (fun N => ‖synthesis (μ N) d‖^2) atTop (𝓝 (‖finsuppCoefficientL2 d‖^2)) := by
  constructor
  · intro h d
    have gram (i j : ℕ) : Tendsto (fun N => inner ℂ (synthesis (μ N) (basis i))
        (synthesis (μ N) (basis j))) atTop
        (𝓝 (inner ℂ (finsuppCoefficientL2 (basis i)) (finsuppCoefficientL2 (basis j)))) := by
      simp only [basis_pair,←uniform_pair]
      exact ((continuous_circleMeasureMomentZ _).tendsto uniform).comp h
    have gramSum := tendsto_finsetSum d.support (fun i _ => tendsto_finsetSum d.support
      (fun j _ => (gram i j).const_mul (conj (d i)*d j)))
    have hsq : Tendsto (fun N => inner ℂ (synthesis (μ N) d) (synthesis (μ N) d)) atTop
        (𝓝 (inner ℂ (finsuppCoefficientL2 d) (finsuppCoefficientL2 d))) := by
      simpa only [finite_pair (synthesis _) d d,finite_pair finsuppCoefficientL2 d d] using gramSum
    have hr := Complex.continuous_re.continuousAt.tendsto.comp hsq
    change Tendsto (fun N => (inner ℂ (synthesis (μ N) d) (synthesis (μ N) d)).re) atTop
      (𝓝 (inner ℂ (finsuppCoefficientL2 d) (finsuppCoefficientL2 d)).re) at hr
    have target : (inner ℂ (finsuppCoefficientL2 d) (finsuppCoefficientL2 d)).re =
        ‖finsuppCoefficientL2 d‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [target] at hr
    exact hr.congr (fun N => inner_self_eq_norm_sq (𝕜 := ℂ) (synthesis (μ N) d))
  · intro h
    rw [isClosedEmbedding_completeCircleMomentSequence.isEmbedding.tendsto_nhds_iff,tendsto_pi_nhds]
    intro k
    obtain ⟨i,j,eq⟩ : ∃ i j : ℕ, (i:ℤ)-j=k := ⟨k.toNat,(-k).toNat,by omega⟩
    rw [←eq]
    have gram := pair_of_norms μ h (basis i) (basis j)
    simpa only [Function.comp_def,completeCircleMomentSequence,basis_pair,←uniform_pair] using gram

#print axioms haar_iff_occupation_norms

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
