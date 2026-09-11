import GaloisForLFunctions.HTGeometry.VortexWardOperator
import GaloisForLFunctions.HTGeometry.MultiplicativeTheta

/-!
# Elliptic vortex products and their Ward equations

The explicit finite products of arXiv:2609.09298, equations (2.120), (4.37), and (4.49),
are assembled from the existing multiplicative theta. Degree splitting gives the full charged
coefficient recurrence. The resulting Ward identity retains both degree-zero and resonant
contributions; a regularized annihilator is closed for every parameter. At zero elliptic nome,
the factors specialize exactly to q-Pochhammer products already present in the corpus.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open PowerSeries

/-- Elliptic shifted factorial, with independent elliptic nome and degree shift. -/
def vortexThetaPochhammer (p : EulerNome) (a q : ℂ) (d : ℕ) : ℂ :=
  ∏ k ∈ Finset.range d, multiplicativeTheta p (a * q ^ k)

theorem vortexThetaPochhammer_succ (p : EulerNome) (a q : ℂ) (d : ℕ) :
    vortexThetaPochhammer p a q (d + 1) =
      vortexThetaPochhammer p a q d * multiplicativeTheta p (a * q ^ d) := by
  exact Finset.prod_range_succ _ _

/-- Splitting a vortex degree splits the elliptic Euler product into two shifted blocks. -/
theorem vortexThetaPochhammer_add (p : EulerNome) (a q : ℂ) (d e : ℕ) :
    vortexThetaPochhammer p a q (d + e) =
      vortexThetaPochhammer p a q d * vortexThetaPochhammer p (a * q ^ d) q e := by
  simp only [vortexThetaPochhammer, Finset.prod_range_add, pow_add, mul_assoc]

def vortexThetaDenominator {m : ℕ} (p : EulerNome) (q : ℂ) (x : Fin m → ℂ)
    (d : ℕ) : ℂ := ∏ i, multiplicativeTheta p (x i * q⁻¹ ^ d)

def vortexThetaNumerator {r : ℕ} (p : EulerNome) (q : ℂ) (y : Fin r → ℂ)
    (l : Fin r → ℕ) (d : ℕ) : ℂ :=
  ∏ j, ∏ k ∈ Finset.range (l j), multiplicativeTheta p (y j * q ^ (d * l j + k))

/-- The explicit numerator contribution of every charged multiplet through degree `d`. -/
def vortexThetaNumeratorProduct {r : ℕ} (p : EulerNome) (q : ℂ)
    (y : Fin r → ℂ) (l : Fin r → ℕ) (d : ℕ) : ℂ :=
  ∏ j, vortexThetaPochhammer p (y j) q (d * l j)

def vortexThetaDenominatorProduct {m : ℕ} (p : EulerNome) (q : ℂ)
    (x : Fin m → ℂ) (d : ℕ) : ℂ :=
  ∏ i, vortexThetaPochhammer p (x i * q⁻¹) q⁻¹ d

theorem vortexThetaNumeratorProduct_succ {r : ℕ} (p : EulerNome) (q : ℂ)
    (y : Fin r → ℂ) (l : Fin r → ℕ) (d : ℕ) :
    vortexThetaNumeratorProduct p q y l (d + 1) =
      vortexThetaNumeratorProduct p q y l d * vortexThetaNumerator p q y l d := by
  simp only [vortexThetaNumeratorProduct, Nat.add_mul, one_mul, vortexThetaPochhammer_add,
    Finset.prod_mul_distrib]
  simp only [vortexThetaNumerator, vortexThetaPochhammer, pow_add, mul_assoc]

theorem vortexThetaDenominatorProduct_succ {m : ℕ} (p : EulerNome) (q : ℂ)
    (x : Fin m → ℂ) (d : ℕ) :
    vortexThetaDenominatorProduct p q x (d + 1) =
      vortexThetaDenominatorProduct p q x d * vortexThetaDenominator p q x (d + 1) := by
  simp only [vortexThetaDenominatorProduct, vortexThetaPochhammer_succ,
    Finset.prod_mul_distrib, vortexThetaDenominator, pow_succ]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

/-- Finite localization product form of the degree coefficients, including zero denominators. -/
theorem vortexTheta_ratio_coefficient {m r : ℕ} (p : EulerNome) (q : ℂ)
    (x : Fin m → ℂ) (y : Fin r → ℂ) (l : Fin r → ℕ) (d : ℕ) :
    coeff d (vortexRatioSeries (vortexThetaDenominator p q x)
      (vortexThetaNumerator p q y l)) =
      vortexThetaNumeratorProduct p q y l d / vortexThetaDenominatorProduct p q x d := by
  induction d with
  | zero => simp [vortexRatioSeries, vortexProductSeries,
      vortexThetaNumeratorProduct, vortexThetaDenominatorProduct, vortexThetaPochhammer]
  | succ d ih =>
    rw [vortexRatioSeries_recurrence, ih, vortexThetaNumeratorProduct_succ,
      vortexThetaDenominatorProduct_succ]
    simp only [mul_div_mul_comm]
    ring

/-- The elliptic vortex operator has an exact boundary term and an exact resonance correction. -/
theorem vortexTheta_exact_ward {m r : ℕ} (p : EulerNome) (q : ℂ)
    (x : Fin m → ℂ) (y : Fin r → ℂ) (l : Fin r → ℕ) :
    vortexWard (vortexThetaDenominator p q x) (vortexThetaNumerator p q y l)
      (vortexRatioSeries (vortexThetaDenominator p q x) (vortexThetaNumerator p q y l)) =
      C (∏ i, multiplicativeTheta p (x i)) -
        vortexResonanceSeries (vortexThetaDenominator p q x) (vortexThetaNumerator p q y l) := by
  simpa [vortexThetaDenominator] using
    vortexRatioSeries_exact_residual (vortexThetaDenominator p q x) (vortexThetaNumerator p q y l)

/-- A closed elliptic Ward annihilator for all charges, degrees, fugacities and resonances. -/
theorem vortexTheta_closed_annihilator {m r : ℕ} (p : EulerNome) (q : ℂ)
    (x : Fin m → ℂ) (y : Fin r → ℂ) (l : Fin r → ℕ) :
    vortexDiagonal (fun d => (d : ℂ)) (vortexDiagonal (vortexThetaDenominator p q x)
      (vortexWard (vortexThetaDenominator p q x) (vortexThetaNumerator p q y l)
        (vortexRatioSeries (vortexThetaDenominator p q x) (vortexThetaNumerator p q y l)))) = 0 :=
  vortexRatioSeries_closed_annihilator _ _

/-- The nodal value of the elliptic nome. -/
def vortexZeroNome : EulerNome := ⟨0, by simp⟩

@[simp] theorem qPochhammerInf_vortexZeroNome (a : ℂ) :
    qPochhammerInf a vortexZeroNome = 1 - a := by
  rw [qPochhammerInf_shift]
  simp [vortexZeroNome, qPochhammerInf]

@[simp] theorem multiplicativeTheta_vortexZeroNome (a : ℂ) :
    multiplicativeTheta vortexZeroNome a = 1 - a := by
  change qPochhammerInf a vortexZeroNome * qPochhammerInf (0 / a) vortexZeroNome = _
  simp

/-- The elliptic Euler product specializes exactly to the existing K-theoretic q-Pochhammer. -/
theorem vortexThetaPochhammer_zero_nome (a : ℂ) (q : EulerNome) (d : ℕ) :
    vortexThetaPochhammer vortexZeroNome a q d = qPochhammer a q d := by
  simp [vortexThetaPochhammer, qPochhammer]

/-- Ward identity for the ordinary generating series of the existing finite q-Pochhammer. -/
theorem qPochhammer_generating_ward (a : ℂ) (q : EulerNome) :
    let F := PowerSeries.mk (qPochhammer a q)
    F - X * (F - C a * rescale (q : ℂ) F) = 1 := by
  dsimp
  have h := vortexProductSeries_ward (fun n => 1 - a * (q : ℂ) ^ n)
  convert h using 1
  ext n
  cases n <;> simp [vortexWard, vortexProductSeries, qPochhammer,
    coeff_succ_X_mul, coeff_rescale, PowerSeries.coeff_C_mul]
  ring

/-- The factorial normalization converts the same q-Pochhammer recursion into a mixed
ordinary-derivative/q-shift equation. -/
theorem qPochhammer_factorial_generating_ward (a : ℂ) (q : EulerNome) :
    let F := PowerSeries.mk (fun n => qPochhammer a q n / (n.factorial : ℂ))
    derivative ℂ F = F - C a * rescale (q : ℂ) F := by
  dsimp
  change derivative ℂ (vortexFactorialSeries (fun n => 1 - a * (q : ℂ) ^ n)) = _
  rw [vortexFactorialSeries_derivative]
  ext n
  simp [vortexFactorialSeries, qPochhammer, coeff_rescale, PowerSeries.coeff_C_mul]
  ring

/-- The fixed-point relation has a vanishing degree-zero theta factor at every elliptic nome. -/
theorem vortexTheta_at_one (p : EulerNome) : multiplicativeTheta p 1 = 0 := by
  have h : qPochhammerInf 1 p = 0 := by
    rw [qPochhammerInf_shift]
    simp
  simp [multiplicativeTheta, h]

/-- Restricting one positive-charge fugacity to the fixed point removes the degree-zero
boundary. The denominator factor still retains all resonant parameter values. -/
theorem vortexTheta_fixed_point_ward {m r : ℕ} (p : EulerNome) (q : ℂ)
    (x : Fin m → ℂ) (y : Fin r → ℂ) (l : Fin r → ℕ) :
    vortexDiagonal (vortexThetaDenominator p q (Fin.cons 1 x))
      (vortexWard (vortexThetaDenominator p q (Fin.cons 1 x)) (vortexThetaNumerator p q y l)
        (vortexRatioSeries (vortexThetaDenominator p q (Fin.cons 1 x))
          (vortexThetaNumerator p q y l))) = 0 := by
  rw [vortexRatioSeries_regularized_ward]
  simp [vortexThetaDenominator, Fin.prod_univ_succ, vortexTheta_at_one]

/-- Exact K-theoretic specialization of the full charged elliptic coefficient formula. -/
theorem vortexKTheory_ratio_coefficient {m r : ℕ} (q : ℂ)
    (x : Fin m → ℂ) (y : Fin r → ℂ) (l : Fin r → ℕ) (d : ℕ) :
    coeff d (vortexRatioSeries (vortexThetaDenominator vortexZeroNome q x)
      (vortexThetaNumerator vortexZeroNome q y l)) =
      (∏ j, ∏ k ∈ Finset.range (d * l j), (1 - y j * q ^ k)) /
        (∏ i, ∏ k ∈ Finset.range d, (1 - x i * q⁻¹ ^ (k + 1))) := by
  rw [vortexTheta_ratio_coefficient]
  simp only [vortexThetaNumeratorProduct, vortexThetaDenominatorProduct,
    vortexThetaPochhammer, multiplicativeTheta_vortexZeroNome]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro k _
  rw [pow_succ]
  ring

end
end GaloisForLFunctions.HTGeometry
