import GaloisForLFunctions.RHTower.SmoothAFEZetaConditionalGramFibres
import GaloisForLFunctions.RHTower.SmoothAFEZetaReflectedFiniteNodeGram

/-!
# Height-independent source mass for the conditional reflected-AFE Gram determinant

Each literal minor coefficient is a signed sum over tuples with the same cofactor product.
The common height contributes the same unit-modulus phase to every tuple in that fibre.
It therefore factors out before taking norms, including when cancellations occur.

The mean conditional determinant is exactly the explicit chi/conductor row scale squared
multiplied by a nonnegative, height-independent arithmetic mass. A lower bound for that
mass and a simultaneous target law are not asserted here.
-/

open Complex Finset Matrix MeasureTheory
namespace RHTower
noncomputable section

private theorem prod_cpow_pos {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 < x i) (z : ℂ) :
    (∏ i ∈ s, (x i : ℂ) ^ z) = ((∏ i ∈ s, x i : ℝ) : ℂ) ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)), Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hx i (Finset.mem_insert_self _ _)).le
        (Finset.prod_nonneg (fun j hj => (hx j (Finset.mem_insert_of_mem hj)).le))]

/-- Height-independent normalized coefficient of one literal cofactor channel. -/
def reflectedPrimalShapeChannelCoefficient
    (d b r : ℝ) (N p : ℕ) (m : Fin N) : ℂ :=
  if (m : ℕ) + 1 ≤ N / p then
    smoothAFECutoff (r * (((p * ((m : ℕ) + 1) : ℕ) : ℝ) / N)) *
      exp ((rightDisplacedLinePt d b - 1) *
        (Real.log (((p * ((m : ℕ) + 1) : ℕ) : ℝ) / N) : ℂ))
  else 0

/-- Signed product-frequency fibre of the height-independent channel shape. -/
def reflectedPrimalShapeDeterminantCoefficient {J : ℕ}
    (d b : Fin J → ℝ) (r : ℝ) (N : ℕ) (p : Fin J → ℕ)
    (q : Fin (N ^ J)) : ℂ :=
  ∑ m ∈ Sieve.powFibre J N q,
    (Matrix.of fun i j => reflectedPrimalShapeChannelCoefficient
      (d j) (b j) r N (p i) (m i)).det

private theorem channel_coefficient_factor
    (d b τ r : ℝ) {N p : ℕ} (hN : 0 < N) (hp : 0 < p) (m : Fin N) :
    smoothAFEZetaRightReflectedPrimalChannelFinCoeff d (τ + b) r N p m =
      (zetaChi (rightDisplacedLinePt d (τ + b)) *
        (N : ℂ) ^ (rightDisplacedLinePt d (τ + b) - 1)) *
      ((((p * ((m : ℕ) + 1) : ℕ) : ℝ) / N : ℝ) : ℂ) ^ ((τ : ℂ) * I) *
      reflectedPrimalShapeChannelCoefficient d b r N p m := by
  unfold smoothAFEZetaRightReflectedPrimalChannelFinCoeff reflectedPrimalShapeChannelCoefficient
  split_ifs with h
  · rw [reflectedPrimalPositiveCoefficient_factor _ _ _ _ hN
      (Nat.mul_pos hp (Nat.succ_pos _))]
    ring
  · simp

/-- Common height contributes one common scalar to each complete product-frequency fibre.
No term is removed or estimated before the signed fibre sum is formed. -/
theorem reflectedPrimalChannelDeterminantCoefficient_factor {J : ℕ}
    (d b : Fin J → ℝ) (τ r : ℝ) {N : ℕ} (hN : 0 < N)
    (p : Fin J → ℕ) (hp : ∀ i, 0 < p i) (q : Fin (N ^ J)) :
    reflectedPrimalChannelDeterminantCoefficient d (fun j => τ + b j) r N p q =
      (∏ j, zetaChi (rightDisplacedLinePt (d j) (τ + b j)) *
        (N : ℂ) ^ (rightDisplacedLinePt (d j) (τ + b j) - 1)) *
      (((∏ i, (p i : ℝ)) * ((q : ℕ) + 1) / (N : ℝ) ^ J : ℝ) : ℂ) ^
        ((τ : ℂ) * I) *
      reflectedPrimalShapeDeterminantCoefficient d b r N p q := by
  classical
  let A : Fin J → ℂ := fun j =>
    zetaChi (rightDisplacedLinePt (d j) (τ + b j)) *
      (N : ℂ) ^ (rightDisplacedLinePt (d j) (τ + b j) - 1)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  unfold reflectedPrimalChannelDeterminantCoefficient reflectedPrimalShapeDeterminantCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hidx : Sieve.dirichletPowerConvolutionPowIdx m = q :=
    (Finset.mem_filter.mp hm).2
  have hprod : (∏ i, (((m i : ℕ) + 1 : ℕ) : ℝ)) = (q : ℕ) + 1 := by
    have h := Sieve.dirichletPowerConvolutionPowIdx_val_add_one m
    rw [hidx] at h
    exact_mod_cast h.symm
  let x : Fin J → ℝ := fun i => ((p i * ((m i : ℕ) + 1) : ℕ) : ℝ) / N
  have hx : ∀ i, 0 < x i := by
    intro i
    exact div_pos (by exact_mod_cast Nat.mul_pos (hp i) (Nat.succ_pos _)) hNR
  have hmat : (Matrix.of fun i j =>
      smoothAFEZetaRightReflectedPrimalChannelFinCoeff (d j) (τ + b j) r N (p i) (m i)) =
      Matrix.of (fun i j => (x i : ℂ) ^ ((τ : ℂ) * I) *
        (A j * reflectedPrimalShapeChannelCoefficient (d j) (b j) r N (p i) (m i))) := by
    ext i j
    change smoothAFEZetaRightReflectedPrimalChannelFinCoeff (d j) (τ + b j) r N (p i) (m i) = _
    rw [channel_coefficient_factor _ _ _ _ hN (hp i)]
    change A j * (x i : ℂ) ^ ((τ : ℂ) * I) *
      reflectedPrimalShapeChannelCoefficient (d j) (b j) r N (p i) (m i) =
      (x i : ℂ) ^ ((τ : ℂ) * I) *
        (A j * reflectedPrimalShapeChannelCoefficient (d j) (b j) r N (p i) (m i))
    ring
  rw [hmat, Matrix.det_mul_column]
  change (∏ i, (x i : ℂ) ^ ((τ : ℂ) * I)) *
    (Matrix.of fun i j => A j * reflectedPrimalShapeChannelCoefficient
      (d j) (b j) r N (p i) (m i)).det = _
  rw [Matrix.det_mul_row, prod_cpow_pos _ _ (fun i _ => hx i)]
  have hprodX : (∏ i, x i) = (∏ i, (p i : ℝ)) * ((q : ℕ) + 1) / (N : ℝ) ^ J := by
    simp only [x, Nat.cast_mul, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, hprod]
  rw [hprodX]
  change _ * (_ * (Matrix.of fun i j => reflectedPrimalShapeChannelCoefficient
    (d j) (b j) r N (p i) (m i)).det) = _
  dsimp only [A]
  ring

/-- The norm of each complete signed frequency fibre has no common-height phase. -/
theorem norm_reflectedPrimalChannelDeterminantCoefficient_eq_shape {J : ℕ}
    (d b : Fin J → ℝ) (τ r : ℝ) {N : ℕ} (hN : 0 < N)
    (p : Fin J → ℕ) (hp : ∀ i, 0 < p i) (q : Fin (N ^ J)) :
    ‖reflectedPrimalChannelDeterminantCoefficient d (fun j => τ + b j) r N p q‖ =
      (∏ j, ‖zetaChi (rightDisplacedLinePt (d j) (τ + b j))‖ *
        (N : ℝ) ^ (d j - 1 / 2)) *
      ‖reflectedPrimalShapeDeterminantCoefficient d b r N p q‖ := by
  rw [reflectedPrimalChannelDeterminantCoefficient_factor d b τ r hN p hp q,
    norm_mul, norm_mul, norm_prod]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : ∀ i, (0 : ℝ) < p i := fun i => by exact_mod_cast hp i
  have hprodpos : (0 : ℝ) < ∏ i, (p i : ℝ) := Finset.prod_pos (fun i _ => hpR i)
  have hphase : ‖(((∏ i, (p i : ℝ)) * ((q : ℕ) + 1) / (N : ℝ) ^ J : ℝ) : ℂ) ^
      ((τ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp
  rw [hphase, mul_one]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [norm_mul]
  have hpow := Complex.norm_cpow_eq_rpow_re_of_pos hNR
    (rightDisplacedLinePt (d j) (τ + b j) - 1)
  have hre : (rightDisplacedLinePt (d j) (τ + b j) - 1).re = d j - 1 / 2 := by
    simp only [Complex.sub_re, rightDisplacedLinePt_re, Complex.one_re]
    ring
  rw [hre] at hpow
  exact congrArg (fun z => ‖zetaChi (rightDisplacedLinePt (d j) (τ + b j))‖ * z) hpow

/-- The deterministic, height-independent signed-fibre mass of all conditional minors. -/
def reflectedPrimalConditionalShapeMass {J : ℕ} (P : Finset ℕ)
    (d b : Fin J → ℝ) (r : ℝ) (N : ℕ) : ℝ :=
  ∑ s : Set.powersetCard (↥P) J, ∑ q : Fin (N ^ J),
    ‖reflectedPrimalShapeDeterminantCoefficient d b r N
      (fun j => (Set.powersetCard.ofFinEmbEquiv.symm s j : ℕ)) q‖ ^ 2

/-- Exact deterministic formula for the mean conditional determinant at a common height.
The only height dependence is the explicit product of chi and conductor row norms. -/
theorem integral_reflectedPrimalConditionalGram_det_eq_shape {J : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (d b : Fin J → ℝ) (τ r : ℝ) {N : ℕ} (hN : 0 < N) :
    (∫ omega, (reflectedPrimalConditionalGram P d (fun j => τ + b j) r N omega).det.re
        ∂SteinhausModel.steinhausMeasure) =
      (∏ j, ‖zetaChi (rightDisplacedLinePt (d j) (τ + b j))‖ *
        (N : ℝ) ^ (d j - 1 / 2)) ^ 2 *
      reflectedPrimalConditionalShapeMass P d b r N := by
  rw [integral_reflectedPrimalConditionalGram_det]
  unfold reflectedPrimalConditionalGramCoefficient reflectedPrimalConditionalShapeMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [norm_reflectedPrimalChannelDeterminantCoefficient_eq_shape d b τ r hN _
    (fun j => hP _ (Set.powersetCard.ofFinEmbEquiv.symm s j).property) q, mul_pow]

end
end RHTower
