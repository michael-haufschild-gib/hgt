import GaloisForLFunctions.RHTower.CHMDStationaryLocalOperatorDomain
import GaloisForLFunctions.RHTower.CHMDStationaryKernelRigidity
import GaloisForLFunctions.RHTower.CHMDThetaHarmonicIdentity
import GaloisForLFunctions.RHTower.CHMDFarFieldEnergy

/-!
# Harmonic Ground Potential and the Maximal-Domain Prime Shift Form

This module connects the pointwise harmonic identity of the theta kernel (`theta_harmonic_identity`)
to the maximal-domain ground potential (`thetaGroundPotential`, `groundPotentialOperator`),
the bounded prime generator (`primeGenerator`), and the stationary pullback generator
(`stationaryGenerator`):

1. **Exact Pointwise Harmonic Ground-Potential Identity**:
   the archimedean ground-state second-difference integral satisfies
   $$\int_0^\infty \omega(u)\,\Delta_u^2\Theta(x)\,du
     = \cosh(x/2) - \operatorname{primeKernelSum}(x) - c_{\mathrm{arch}}\,\Theta(x),$$
   where $c_{\mathrm{arch}} = 2\,\mathrm{archConstantReal} + 2\int_0^\infty (\omega(u) - \nu(u))\,du > 0$.
   Consequently, for every $x \in \mathbb{R}$,
   $$\operatorname{thetaGroundPotential}(x)
     = 1 - \frac{\operatorname{primeKernelSum}(x) + c_{\mathrm{arch}}\,\Theta(x)}{\cosh(x/2)} < 1.$$
2. **Bounded Prime Diagonal and Prime Shift Operators on `MassSpace`**:
   the ratio $\operatorname{primeDiagonalPotential}(x) = \operatorname{primeKernelSum}(x)/\cosh(x/2)$
   satisfies $0 \le \operatorname{primeDiagonalPotential}(x) \le 1 + \operatorname{thetaGroundPotentialBound}$,
   defining a positive self-adjoint multiplication operator `primeDiagonalOperator` on `MassSpace`
   and the bounded self-adjoint prime shift operator
   `primeShiftOperator = primeDiagonalOperator - primeGenerator` satisfying
   $$I - \operatorname{groundPotentialOperator}
     = \operatorname{primeDiagonalOperator} + \operatorname{archDiagonalOperator}$$
   and
   $$\operatorname{groundPerturbation} - I
     = -\operatorname{primeShiftOperator} - \operatorname{archDiagonalOperator},$$
   where $\operatorname{archDiagonalOperator} = c_{\mathrm{arch}} \bullet (\operatorname{thetaToVolume}^* \circ \operatorname{thetaToVolume})$.
3. **Maximal-Domain Operator and Form Decomposition in Stationary Coordinates**:
   on the common maximal operator domain $\operatorname{arithmeticGenerator}.\mathrm{domain} = \operatorname{stationaryGenerator}.\mathrm{domain}$,
   $$\operatorname{arithmeticGenerator} u - u
     = \operatorname{stationaryGenerator} u - \operatorname{archDiagonalOperator} u - \operatorname{primeShiftOperator} u,$$
   and on `SourceGraph`,
   $$\operatorname{sourceEnergy}(p)
     = \operatorname{stationaryEnergy}(\Theta \cdot p.\mathrm{fst})
       - c_{\mathrm{arch}}\,\|\operatorname{thetaToVolume}(p.\mathrm{fst})\|_{L^2(\mathbb{R})}^2
       - \langle \operatorname{primeShiftOperator}(p.\mathrm{fst}), p.\mathrm{fst}\rangle_{\mathrm{MassSpace}}.$$
4. **Explicit Edge-Measure Formula for `primeShiftOperator`**:
   for all $u \in \mathrm{MassSpace}$,
   $$\langle \operatorname{primeShiftOperator} u, u\rangle_{\mathrm{MassSpace}}
     = 2 \int e,\, u(\operatorname{left} e)\,u(\operatorname{right} e)\,d\mathrm{allPrimeMeasure}(e),$$
   with $|\langle \operatorname{primeShiftOperator} u, u\rangle| \le \langle \operatorname{primeDiagonalOperator} u, u\rangle$.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace BigOperators
noncomputable section

namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump ThetaSourceWard

/-! ## Section 1: Exact Pointwise Harmonic Formula for `thetaGroundPotential` -/

/-- The positive archimedean density difference `ω(u) - ν(u) = (e^{-u/2} - e^{-2u}) / (1 - e^{-2u})`. -/
def archLevySubDiagonal (u : ℝ) : ℝ :=
  archLevyDensity u - archDiagonalDensity u

theorem archLevySubDiagonal_pos {u : ℝ} (hu : 0 < u) : 0 < archLevySubDiagonal u := by
  unfold archLevySubDiagonal archLevyDensity archDiagonalDensity
  rw [← sub_div]
  have hden : 0 < 1 - Real.exp (-2 * u) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hnum : 0 < Real.exp (-u / 2) - Real.exp (-2 * u) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  exact div_pos hnum hden

theorem archLevySubDiagonal_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ archLevySubDiagonal u :=
  (archLevySubDiagonal_pos hu).le

/-- Algebraic bridge between the maximal-domain ground-potential integrand
`archLevyDensity u * thetaSecondDifference u x` and `symArchTerm x u`. -/
theorem thetaSecondDifference_kernel_add_symArchTerm (u x : ℝ) :
    archLevyDensity u * thetaSecondDifference u x + symArchTerm x u =
      -2 * riemannKernelReal x * archLevySubDiagonal u := by
  unfold thetaSecondDifference symArchTerm archLevySubDiagonal
  ring

theorem integrableOn_archLevySubDiagonal : IntegrableOn archLevySubDiagonal (Ioi (0 : ℝ)) := by
  have h1 := integrable_thetaSecondDifference_kernel 0
  have h2 := integrableOn_symArchTerm 0
  have hsum : IntegrableOn
      (fun u => (-2 * riemannKernelReal 0)⁻¹ *
        (archLevyDensity u * thetaSecondDifference u 0 + symArchTerm 0 u)) (Ioi (0 : ℝ)) :=
    (h1.add h2).const_mul ((-2 * riemannKernelReal 0)⁻¹)
  refine hsum.congr_fun (fun u _ => ?_) measurableSet_Ioi
  have hne : -2 * riemannKernelReal 0 ≠ 0 :=
    mul_ne_zero (by norm_num) (riemannKernelReal_pos 0).ne'
  dsimp only [Pi.add_apply]
  rw [thetaSecondDifference_kernel_add_symArchTerm, inv_mul_cancel_left₀ hne]

theorem integral_archLevySubDiagonal_nonneg :
    0 ≤ ∫ u in Ioi (0 : ℝ), archLevySubDiagonal u :=
  setIntegral_nonneg measurableSet_Ioi fun _ hu => archLevySubDiagonal_nonneg hu

theorem archConstantReal_pos : 0 < archConstantReal := by
  unfold archConstantReal
  have hγ : (1 : ℝ) / 2 < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
  have hπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  linarith

/-- The strictly positive archimedean ground constant
`c_arch = γ + log π + 2 ∫_0^∞ (ω(u) - ν(u)) du > 0`. -/
def archGroundConstant : ℝ :=
  2 * archConstantReal + 2 * ∫ u in Ioi (0 : ℝ), archLevySubDiagonal u

theorem archGroundConstant_pos : 0 < archGroundConstant := by
  unfold archGroundConstant
  linarith [archConstantReal_pos, integral_archLevySubDiagonal_nonneg]

theorem primeKernelSum_term_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ vonMangoldtAtom n *
      (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n)) :=
  mul_nonneg (vonMangoldtAtom_nonneg n)
    (add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le)

theorem primeKernelSum_nonneg (x : ℝ) : 0 ≤ primeKernelSum x :=
  tsum_nonneg (primeKernelSum_term_nonneg x)

/-- **Exact Evaluation of the Archimedean Ground-State Second-Difference Integral**:
for every `x : ℝ`,
`∫_{u > 0} ω(u) (Θ(x+u) + Θ(x-u) - 2Θ(x)) du = cosh(x / 2) - primeKernelSum x - archGroundConstant * Θ(x)`. -/
theorem integral_thetaSecondDifference_kernel_eq (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), archLevyDensity u * thetaSecondDifference u x) =
      Real.cosh (x / 2) - primeKernelSum x - archGroundConstant * riemannKernelReal x := by
  have hadd : (∫ u in Ioi (0 : ℝ), archLevyDensity u * thetaSecondDifference u x) +
      (∫ u in Ioi (0 : ℝ), symArchTerm x u) =
      -2 * riemannKernelReal x * ∫ u in Ioi (0 : ℝ), archLevySubDiagonal u := by
    rw [← integral_add (integrable_thetaSecondDifference_kernel x) (integrableOn_symArchTerm x),
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    exact thetaSecondDifference_kernel_add_symArchTerm u x
  have hharm := theta_harmonic_identity x
  unfold archGroundConstant
  linarith

/-- **Exact Pointwise Harmonic Ground-Potential Identity**:
for every `x : ℝ`,
`thetaGroundPotential x = 1 - (primeKernelSum x + archGroundConstant * Θ(x)) / cosh(x / 2)`. -/
theorem thetaGroundPotential_eq_harmonic (x : ℝ) :
    thetaGroundPotential x =
      1 - (primeKernelSum x + archGroundConstant * riemannKernelReal x) / Real.cosh (x / 2) := by
  unfold thetaGroundPotential
  rw [integral_thetaSecondDifference_kernel_eq x]
  have hch : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos (x / 2)).ne'
  field_simp [hch]
  ring

theorem one_sub_thetaGroundPotential_eq (x : ℝ) :
    1 - thetaGroundPotential x =
      (primeKernelSum x + archGroundConstant * riemannKernelReal x) / Real.cosh (x / 2) := by
  rw [thetaGroundPotential_eq_harmonic]
  ring

theorem one_sub_thetaGroundPotential_pos (x : ℝ) : 0 < 1 - thetaGroundPotential x := by
  rw [one_sub_thetaGroundPotential_eq]
  refine div_pos ?_ (Real.cosh_pos (x / 2))
  exact add_pos_of_nonneg_of_pos (primeKernelSum_nonneg x)
    (mul_pos archGroundConstant_pos (riemannKernelReal_pos x))

theorem thetaGroundPotential_lt_one (x : ℝ) : thetaGroundPotential x < 1 :=
  sub_pos.mp (one_sub_thetaGroundPotential_pos x)

theorem primeKernelSum_div_cosh_nonneg (x : ℝ) :
    0 ≤ primeKernelSum x / Real.cosh (x / 2) :=
  div_nonneg (primeKernelSum_nonneg x) (Real.cosh_pos (x / 2)).le

theorem primeKernelSum_div_cosh_lt_one_sub_thetaGroundPotential (x : ℝ) :
    primeKernelSum x / Real.cosh (x / 2) < 1 - thetaGroundPotential x := by
  rw [one_sub_thetaGroundPotential_eq, add_div]
  have hpos : 0 < archGroundConstant * riemannKernelReal x / Real.cosh (x / 2) :=
    div_pos (mul_pos archGroundConstant_pos (riemannKernelReal_pos x)) (Real.cosh_pos (x / 2))
  linarith

theorem primeKernelSum_div_cosh_le (x : ℝ) :
    primeKernelSum x / Real.cosh (x / 2) ≤ 1 + thetaGroundPotentialBound := by
  have h1 := (primeKernelSum_div_cosh_lt_one_sub_thetaGroundPotential x).le
  have h2 := norm_thetaGroundPotential_le x
  rw [Real.norm_eq_abs] at h2
  have h3 := neg_le_of_abs_le h2
  linarith

/-! ## Section 2: Bounded Prime Diagonal and Prime Shift Operators on `MassSpace` -/

/-- The bounded nonnegative prime diagonal multiplier
`primeDiagonalPotential x = primeKernelSum x / cosh(x / 2)`. -/
def primeDiagonalPotential (x : ℝ) : ℝ :=
  primeKernelSum x / Real.cosh (x / 2)

def primeDiagonalPotentialBound : ℝ :=
  1 + thetaGroundPotentialBound

theorem primeDiagonalPotentialBound_nonneg : 0 ≤ primeDiagonalPotentialBound := by
  unfold primeDiagonalPotentialBound
  linarith [thetaGroundPotentialBound_nonneg]

theorem measurable_primeDiagonalPotential : Measurable primeDiagonalPotential :=
  measurable_primeKernelSum.div (Real.continuous_cosh.comp (continuous_id.div_const 2)).measurable

theorem primeDiagonalPotential_nonneg (x : ℝ) : 0 ≤ primeDiagonalPotential x :=
  primeKernelSum_div_cosh_nonneg x

theorem norm_primeDiagonalPotential_le (x : ℝ) :
    ‖primeDiagonalPotential x‖ ≤ primeDiagonalPotentialBound := by
  rw [Real.norm_of_nonneg (primeDiagonalPotential_nonneg x)]
  exact primeKernelSum_div_cosh_le x

/-- The bounded self-adjoint positive multiplication operator on `MassSpace` with symbol
`primeDiagonalPotential`. -/
def primeDiagonalOperator : MassSpace →L[ℝ] MassSpace :=
  lpBoundedMulCLM measurable_primeDiagonalPotential primeDiagonalPotentialBound_nonneg
    norm_primeDiagonalPotential_le

theorem primeDiagonalOperator_ae (u : MassSpace) :
    primeDiagonalOperator u =ᵐ[massMeasure] fun x => primeDiagonalPotential x * u x :=
  lpBoundedMulCLM_coeFn _ _ _ u

theorem primeDiagonalOperator_symmetric (u v : MassSpace) :
    ⟪primeDiagonalOperator u, v⟫_ℝ = ⟪u, primeDiagonalOperator v⟫_ℝ :=
  lpBoundedMulCLM_inner_real _ _ _ (fun _ => rfl) u v

theorem inner_primeDiagonalOperator (u v : MassSpace) :
    ⟪primeDiagonalOperator u, v⟫_ℝ =
      ∫ x, primeDiagonalPotential x * u x * v x ∂massMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [primeDiagonalOperator_ae u] with x hx
  simp only [hx, RCLike.inner_apply', conj_trivial]

theorem inner_primeDiagonalOperator_self (u : MassSpace) :
    ⟪primeDiagonalOperator u, u⟫_ℝ =
      ∫ x, primeDiagonalPotential x * u x ^ 2 ∂massMeasure := by
  rw [inner_primeDiagonalOperator]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem inner_primeDiagonalOperator_self_eq_volume (u : MassSpace) :
    ⟪primeDiagonalOperator u, u⟫_ℝ =
      ∫ x, primeKernelSum x * riemannKernelReal x * u x ^ 2 := by
  rw [inner_primeDiagonalOperator_self, integral_mass]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold massDensity primeDiagonalPotential
  have hch : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos (x / 2)).ne'
  field_simp [hch]

theorem primeDiagonalOperator_isPositive : primeDiagonalOperator.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨primeDiagonalOperator_symmetric, fun u => ?_⟩
  rw [inner_primeDiagonalOperator_self]
  exact integral_nonneg fun x => mul_nonneg (primeDiagonalPotential_nonneg x) (sq_nonneg _)

theorem primeDiagonalOperator_isSelfAdjoint : IsSelfAdjoint primeDiagonalOperator :=
  primeDiagonalOperator_isPositive.isSelfAdjoint

/-- The bounded archimedean diagonal operator
`archDiagonalOperator = archGroundConstant • (thetaToVolume.adjoint ∘L thetaToVolume)` on `MassSpace`. -/
def archDiagonalOperator : MassSpace →L[ℝ] MassSpace :=
  archGroundConstant • (thetaToVolume.adjoint.comp thetaToVolume)

theorem inner_archDiagonalOperator (u v : MassSpace) :
    ⟪archDiagonalOperator u, v⟫_ℝ =
      archGroundConstant * ⟪thetaToVolume u, thetaToVolume v⟫_ℝ := by
  change ⟪archGroundConstant • thetaToVolume.adjoint (thetaToVolume u), v⟫_ℝ = _
  rw [real_inner_smul_left, thetaToVolume.adjoint_inner_left]

theorem inner_archDiagonalOperator_self (u : MassSpace) :
    ⟪archDiagonalOperator u, u⟫_ℝ = archGroundConstant * ‖thetaToVolume u‖ ^ 2 := by
  rw [inner_archDiagonalOperator, real_inner_self_eq_norm_sq]

theorem inner_archDiagonalOperator_eq_volume (u v : MassSpace) :
    ⟪archDiagonalOperator u, v⟫_ℝ =
      archGroundConstant * ∫ x, thetaProduct u x * thetaProduct v x := by
  rw [inner_archDiagonalOperator, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [thetaToVolume_ae u, thetaToVolume_ae v] with x hu hv
  simp only [hu, hv, RCLike.inner_apply', conj_trivial]

theorem inner_archDiagonalOperator_eq_mass (u v : MassSpace) :
    ⟪archDiagonalOperator u, v⟫_ℝ =
      ∫ x, (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) * u x * v x ∂massMeasure := by
  rw [inner_archDiagonalOperator_eq_volume, integral_mass, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold massDensity thetaProduct
  have hch : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos (x / 2)).ne'
  field_simp [hch]

theorem archDiagonalOperator_symmetric (u v : MassSpace) :
    ⟪archDiagonalOperator u, v⟫_ℝ = ⟪u, archDiagonalOperator v⟫_ℝ := by
  rw [real_inner_comm (archDiagonalOperator v), inner_archDiagonalOperator,
    inner_archDiagonalOperator, real_inner_comm]

theorem archDiagonalOperator_isPositive : archDiagonalOperator.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨archDiagonalOperator_symmetric, fun u => ?_⟩
  rw [inner_archDiagonalOperator_self]
  exact mul_nonneg archGroundConstant_pos.le (sq_nonneg _)

theorem archDiagonalOperator_isSelfAdjoint : IsSelfAdjoint archDiagonalOperator :=
  archDiagonalOperator_isPositive.isSelfAdjoint

theorem inner_groundPotentialOperator (u v : MassSpace) :
    ⟪groundPotentialOperator u, v⟫_ℝ =
      ∫ x, thetaGroundPotential x * u x * v x ∂massMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [groundPotentialOperator_ae u] with x hx
  simp only [hx, RCLike.inner_apply', conj_trivial]

/-- **Operator Harmonic Decomposition of `groundPotentialOperator`**:
on `MassSpace`, `I - groundPotentialOperator = primeDiagonalOperator + archDiagonalOperator`. -/
theorem sub_groundPotentialOperator_eq :
    ContinuousLinearMap.id ℝ MassSpace - groundPotentialOperator =
      primeDiagonalOperator + archDiagonalOperator := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  change ⟪u - groundPotentialOperator u, v⟫_ℝ =
    ⟪primeDiagonalOperator u + archDiagonalOperator u, v⟫_ℝ
  rw [inner_sub_left, inner_add_left,
    inner_groundPotentialOperator, inner_primeDiagonalOperator,
    inner_archDiagonalOperator_eq_mass, L2.inner_def]
  have hint_u_v : Integrable (fun x => u x * v x) massMeasure := by
    refine (L2.integrable_inner u v).congr ?_
    filter_upwards [] with x
    simp [mul_comm]
  have hint_g : Integrable (fun x => thetaGroundPotential x * u x * v x) massMeasure := by
    refine (L2.integrable_inner (groundPotentialOperator u) v).congr ?_
    filter_upwards [groundPotentialOperator_ae u] with x hx
    simp only [hx, RCLike.inner_apply', conj_trivial]
  have hint_p : Integrable (fun x => primeDiagonalPotential x * u x * v x) massMeasure := by
    refine (L2.integrable_inner (primeDiagonalOperator u) v).congr ?_
    filter_upwards [primeDiagonalOperator_ae u] with x hx
    simp only [hx, RCLike.inner_apply', conj_trivial]
  have hint_a : Integrable
      (fun x => (archGroundConstant * riemannKernelReal x / Real.cosh (x / 2)) * u x * v x)
      massMeasure := by
    have h := (Lp.memLp (thetaToVolume u)).integrable_mul (Lp.memLp (thetaToVolume v))
    rw [integrable_mass_iff]
    refine (h.const_mul archGroundConstant).congr ?_
    filter_upwards [thetaToVolume_ae u, thetaToVolume_ae v] with x hu hv
    dsimp only [Pi.mul_apply]
    rw [hu, hv]
    unfold massDensity thetaProduct
    have hch : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos (x / 2)).ne'
    field_simp [hch]
  have huv_eq : (∫ x, inner ℝ (u x) (v x) ∂massMeasure) = ∫ x, u x * v x ∂massMeasure := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [mul_comm]
  rw [huv_eq, ← integral_sub hint_u_v hint_g, ← integral_add hint_p hint_a]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [thetaGroundPotential_eq_harmonic x]
  unfold primeDiagonalPotential
  ring

/-- **The Bounded Self-Adjoint Prime Shift Operator on `MassSpace`**:
`primeShiftOperator = primeDiagonalOperator - primeGenerator`. -/
def primeShiftOperator : MassSpace →L[ℝ] MassSpace :=
  primeDiagonalOperator - primeGenerator

theorem primeShiftOperator_symmetric (u v : MassSpace) :
    ⟪primeShiftOperator u, v⟫_ℝ = ⟪u, primeShiftOperator v⟫_ℝ := by
  change ⟪primeDiagonalOperator u - primeGenerator u, v⟫_ℝ =
    ⟪u, primeDiagonalOperator v - primeGenerator v⟫_ℝ
  rw [inner_sub_left, inner_sub_right, primeDiagonalOperator_symmetric,
    real_inner_comm (primeGenerator v), inner_primeGenerator,
    inner_primeGenerator, real_inner_comm (primeDifference v)]

theorem primeShiftOperator_isSelfAdjoint : IsSelfAdjoint primeShiftOperator :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr primeShiftOperator_symmetric

/-- **Exact Operator Decomposition of `groundPerturbation - I`**:
on `MassSpace`, `groundPerturbation - I = -primeShiftOperator - archDiagonalOperator`. -/
theorem groundPerturbation_sub_id_eq :
    groundPerturbation - ContinuousLinearMap.id ℝ MassSpace =
      -primeShiftOperator - archDiagonalOperator := by
  have h := sub_groundPotentialOperator_eq
  unfold groundPerturbation primeShiftOperator
  have h2 : groundPotentialOperator =
      ContinuousLinearMap.id ℝ MassSpace - (primeDiagonalOperator + archDiagonalOperator) := by
    rw [← h, sub_sub_cancel]
  rw [h2]
  abel

/-! ## Section 3: Maximal-Domain Operator and Form Decomposition in Stationary Coordinates -/

/-- **Maximal-Domain Operator Identity for `arithmeticGenerator - I`**:
for every `u ∈ arithmeticGenerator.domain`,
`arithmeticGenerator u - u = stationaryGenerator u - archDiagonalOperator u - primeShiftOperator u`. -/
theorem arithmeticGenerator_sub_id_eq_stationary (u : arithmeticGenerator.domain) :
    arithmeticGenerator u - (u : MassSpace) =
      stationaryGenerator ⟨(u : MassSpace), arithmeticGenerator_domain_eq_stationary ▸ u.property⟩ -
        archDiagonalOperator u - primeShiftOperator u := by
  rw [arithmeticGenerator_eq_stationary_add u]
  have h := congrArg (fun T : MassSpace →L[ℝ] MassSpace => T u) groundPerturbation_sub_id_eq
  change groundPerturbation u - (u : MassSpace) =
    -primeShiftOperator u - archDiagonalOperator u at h
  have h2 : groundPerturbation u =
      -primeShiftOperator u - archDiagonalOperator u + (u : MassSpace) :=
    sub_eq_iff_eq_add.mp h
  rw [h2]
  abel

/-- Every eigenvector `resolvent w = μ • w` with `μ ≠ 0` lies in `arithmeticGenerator.domain`. -/
theorem mem_arithmeticGenerator_domain_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) : w ∈ arithmeticGenerator.domain := by
  refine ⟨μ⁻¹ • w, ?_⟩
  change resolvent (μ⁻¹ • w) = w
  rw [map_smul, heig, inv_smul_smul₀ hμ]

theorem arithmeticGenerator_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    arithmeticGenerator ⟨w, mem_arithmeticGenerator_domain_of_eigenvector hμ heig⟩ =
      ((1 - μ) / μ) • w := by
  have h1 : (⟨w, mem_arithmeticGenerator_domain_of_eigenvector hμ heig⟩ :
      arithmeticGenerator.domain) =
      ⟨resolvent (μ⁻¹ • w), ⟨μ⁻¹ • w, rfl⟩⟩ :=
    Subtype.ext (by change w = resolvent (μ⁻¹ • w); rw [map_smul, heig, inv_smul_smul₀ hμ])
  rw [h1, arithmeticGenerator_resolvent, map_smul, heig, inv_smul_smul₀ hμ]
  nth_rw 2 [← one_smul ℝ w]
  rw [← sub_smul]
  congr 1
  field_simp [hμ]

/-- **Stationary Operator Equation for Resolvent Eigenvectors**:
for every eigenvector `resolvent w = μ • w` with `μ ≠ 0`, `w` lies in `stationaryGenerator.domain`
and satisfies
`stationaryGenerator w - archDiagonalOperator w - primeShiftOperator w = ((1 - 2 * μ) / μ) • w`. -/
theorem stationaryGenerator_sub_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    stationaryGenerator
      ⟨w, arithmeticGenerator_domain_eq_stationary ▸
        mem_arithmeticGenerator_domain_of_eigenvector hμ heig⟩ -
        archDiagonalOperator w - primeShiftOperator w =
      ((1 - 2 * μ) / μ) • w := by
  have h1 := arithmeticGenerator_sub_id_eq_stationary
    ⟨w, mem_arithmeticGenerator_domain_of_eigenvector hμ heig⟩
  rw [arithmeticGenerator_of_eigenvector hμ heig] at h1
  rw [← h1]
  change ((1 - μ) / μ) • w - w = ((1 - 2 * μ) / μ) • w
  nth_rw 2 [← one_smul ℝ w]
  rw [← sub_smul]
  congr 1
  field_simp [hμ]
  ring

/-- **Maximal-Domain Bilinear Decomposition of `sourcePair` in Stationary Coordinates**:
for all `p, q : SourceGraph`,
`sourcePair p q = ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ - archGroundConstant * ⟪thetaToVolume p.val.fst, thetaToVolume q.val.fst⟫_ℝ - ⟪primeShiftOperator p.val.fst, q.val.fst⟫_ℝ`. -/
theorem sourcePair_eq_stationary_sub_arch_sub_primeShift (p q : SourceGraph) :
    sourcePair p q =
      ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ -
        archGroundConstant * ⟪thetaToVolume p.val.fst, thetaToVolume q.val.fst⟫_ℝ -
        ⟪primeShiftOperator p.val.fst, q.val.fst⟫_ℝ := by
  have h1 := fullGround_inner_decomposition p q
  rw [graph_inner] at h1
  have hstat : ⟪fullGroundEquiv p, fullGroundEquiv q⟫_ℝ =
      ⟪p.val.fst, q.val.fst⟫_ℝ + ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ := by
    have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
    have hq : (fullGroundEquiv q).val.fst = q.val.fst := fullGroundEquiv_source q
    rw [Submodule.coe_inner, WithLp.prod_inner_apply]
    change ⟪(fullGroundEquiv p).val.fst, (fullGroundEquiv q).val.fst⟫_ℝ +
      ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv q).val.snd⟫_ℝ = _
    rw [hp, hq]
  have hpert : ⟪groundPerturbation p.val.fst, q.val.fst⟫_ℝ - ⟪p.val.fst, q.val.fst⟫_ℝ =
      -⟪primeShiftOperator p.val.fst, q.val.fst⟫_ℝ -
        archGroundConstant * ⟪thetaToVolume p.val.fst, thetaToVolume q.val.fst⟫_ℝ := by
    have h2 := congrArg (fun T : MassSpace →L[ℝ] MassSpace => ⟪T p.val.fst, q.val.fst⟫_ℝ)
      groundPerturbation_sub_id_eq
    change ⟪groundPerturbation p.val.fst - p.val.fst, q.val.fst⟫_ℝ =
      ⟪-primeShiftOperator p.val.fst - archDiagonalOperator p.val.fst, q.val.fst⟫_ℝ at h2
    rw [inner_sub_left, inner_sub_left, inner_neg_left, inner_archDiagonalOperator] at h2
    linarith
  change ⟪p.val.snd, q.val.snd⟫_ℝ - ⟪p.val.fst, q.val.fst⟫_ℝ = _
  change ⟪p.val.fst, q.val.fst⟫_ℝ + ⟪p.val.snd, q.val.snd⟫_ℝ =
    ⟪fullGroundEquiv p, fullGroundEquiv q⟫_ℝ +
      ⟪groundPerturbation p.val.fst, q.val.fst⟫_ℝ at h1
  linarith

/-- **Maximal-Domain Decomposition of `sourceEnergy` in Stationary Coordinates**:
for every `p : SourceGraph`,
`sourceEnergy p = stationaryEnergy (thetaProduct p.val.fst) - archGroundConstant * ‖thetaToVolume p.val.fst‖ ^ 2 - ⟪primeShiftOperator p.val.fst, p.val.fst⟫_ℝ`. -/
theorem sourceEnergy_eq_stationary_sub_arch_sub_primeShift (p : SourceGraph) :
    sourceEnergy p =
      stationaryEnergy (thetaProduct p.val.fst) -
        archGroundConstant * ‖thetaToVolume p.val.fst‖ ^ 2 -
        ⟪primeShiftOperator p.val.fst, p.val.fst⟫_ℝ := by
  have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
  rw [← sourcePair_self, sourcePair_eq_stationary_sub_arch_sub_primeShift,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    stationaryGround_edge_energy, hp]

/-! ## Section 4: Explicit Edge-Measure Formula for `primeShiftOperator` -/

theorem integrable_allPrime_left_sq (u : MassSpace) :
    Integrable (fun e => u (left e) ^ 2) allPrimeMeasure :=
  (memLp_allPrime_left (Lp.memLp u)).integrable_sq

theorem integrable_allPrime_right_sq (u : MassSpace) :
    Integrable (fun e => u (right e) ^ 2) allPrimeMeasure :=
  (memLp_allPrime_right (Lp.memLp u)).integrable_sq

theorem integrable_allPrime_left_mul_right (u v : MassSpace) :
    Integrable (fun e => u (left e) * v (right e)) allPrimeMeasure :=
  (memLp_allPrime_left (Lp.memLp u)).integrable_mul (memLp_allPrime_right (Lp.memLp v))

theorem tsum_primeWeight_add_neg (x : ℝ) :
    (∑' n : ℕ, (primeWeight n x + primeWeight n (-x))) =
      primeKernelSum x * riemannKernelReal x := by
  rw [(summable_primeWeight x).tsum_add (summable_primeWeight (-x))]
  have hl : (∑' n : ℕ, primeWeight n x) =
      riemannKernelReal x * ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x + Real.log n) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by unfold primeWeight; ring
  have hr : (∑' n : ℕ, primeWeight n (-x)) =
      riemannKernelReal x * ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (x - Real.log n) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    unfold primeWeight
    rw [WeilExcess.riemannKernelReal_neg,
      show -x + Real.log n = -(x - Real.log n) by ring, WeilExcess.riemannKernelReal_neg]
    ring
  rw [hl, hr, ← mul_add,
    ← (summable_primeShift_right x).tsum_add (summable_primeShift_left x), mul_comm]
  congr 1
  exact tsum_congr fun n => by ring

theorem tsum_ofReal_primeWeight :
    (∑' n : ℕ, fun x : ℝ => ENNReal.ofReal (primeWeight n x)) =
      fun x : ℝ => ENNReal.ofReal (∑' n : ℕ, primeWeight n x) := by
  funext x
  rw [ENNReal.tsum_apply,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => primeWeight_nonneg n x)
      (summable_primeWeight x)]

theorem tsum_ofReal_primeWeight_neg :
    (∑' n : ℕ, fun x : ℝ => ENNReal.ofReal (primeWeight n (-x))) =
      fun x : ℝ => ENNReal.ofReal (∑' n : ℕ, primeWeight n (-x)) := by
  funext x
  rw [ENNReal.tsum_apply,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => primeWeight_nonneg n (-x))
      (summable_primeWeight (-x))]

theorem integral_allPrime_left_sq_add_right_sq (u : MassSpace) :
    (∫ e, (u (left e) ^ 2 + u (right e) ^ 2) ∂allPrimeMeasure) =
      ⟪primeDiagonalOperator u, u⟫_ℝ := by
  have haeL : AEMeasurable left allPrimeMeasure := measurable_snd.aemeasurable
  have haeR : AEMeasurable right allPrimeMeasure := (measurable_snd.add measurable_fst).aemeasurable
  have hmeasL : Measurable fun x : ℝ => ∑' n : ℕ, primeWeight n x :=
    Measurable.tsum fun n => (continuous_primeWeight n).measurable
  have hmeasR : Measurable fun x : ℝ => ∑' n : ℕ, primeWeight n (-x) :=
    Measurable.tsum fun n => ((continuous_primeWeight n).comp continuous_neg).measurable
  have hL : (∫ e, u (left e) ^ 2 ∂allPrimeMeasure) =
      ∫ x, (∑' n : ℕ, primeWeight n x) * u x ^ 2 := by
    have hm : AEStronglyMeasurable (fun x : ℝ => u x ^ 2) (Measure.map left allPrimeMeasure) :=
      ((Lp.aestronglyMeasurable u).pow 2).mono_ac
        (Measure.absolutelyContinuous_of_le_smul map_allPrime_left_le)
    change (∫ e, (fun x : ℝ => u x ^ 2) (left e) ∂allPrimeMeasure) = _
    rw [← integral_map haeL hm, Measure.map_sum haeL]
    simp_rw [map_prime_left]
    rw [← withDensity_tsum (fun n => (continuous_primeWeight n).measurable.ennreal_ofReal),
      tsum_ofReal_primeWeight,
      integral_weighted volume hmeasL
        (Eventually.of_forall fun x => tsum_nonneg fun n => primeWeight_nonneg n x)]
  have hR : (∫ e, u (right e) ^ 2 ∂allPrimeMeasure) =
      ∫ x, (∑' n : ℕ, primeWeight n (-x)) * u x ^ 2 := by
    have hm : AEStronglyMeasurable (fun x : ℝ => u x ^ 2) (Measure.map right allPrimeMeasure) :=
      ((Lp.aestronglyMeasurable u).pow 2).mono_ac
        (Measure.absolutelyContinuous_of_le_smul map_allPrime_right_le)
    change (∫ e, (fun x : ℝ => u x ^ 2) (right e) ∂allPrimeMeasure) = _
    rw [← integral_map haeR hm, Measure.map_sum haeR]
    simp_rw [map_prime_right]
    rw [← withDensity_tsum (fun n => show Measurable
        (fun x : ℝ => ENNReal.ofReal (primeWeight n (-x))) from
          ((continuous_primeWeight n).comp continuous_neg).measurable.ennreal_ofReal),
      tsum_ofReal_primeWeight_neg,
      integral_weighted volume hmeasR
        (Eventually.of_forall fun x => tsum_nonneg fun n => primeWeight_nonneg n (-x))]
  have hintL : Integrable (fun x => (∑' n : ℕ, primeWeight n x) * u x ^ 2) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => u x ^ 2) (Measure.map left allPrimeMeasure) :=
      ((Lp.aestronglyMeasurable u).pow 2).mono_ac
        (Measure.absolutelyContinuous_of_le_smul map_allPrime_left_le)
    have hi := (integrable_map_measure hm haeL).mpr (integrable_allPrime_left_sq u)
    rw [Measure.map_sum haeL] at hi
    simp_rw [map_prime_left] at hi
    rw [← withDensity_tsum (fun n => (continuous_primeWeight n).measurable.ennreal_ofReal),
      tsum_ofReal_primeWeight] at hi
    exact (integrable_weighted_iff volume hmeasL
      (Eventually.of_forall fun x => tsum_nonneg fun n => primeWeight_nonneg n x) _).mp hi
  have hintR : Integrable (fun x => (∑' n : ℕ, primeWeight n (-x)) * u x ^ 2) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => u x ^ 2) (Measure.map right allPrimeMeasure) :=
      ((Lp.aestronglyMeasurable u).pow 2).mono_ac
        (Measure.absolutelyContinuous_of_le_smul map_allPrime_right_le)
    have hi := (integrable_map_measure hm haeR).mpr (integrable_allPrime_right_sq u)
    rw [Measure.map_sum haeR] at hi
    simp_rw [map_prime_right] at hi
    rw [← withDensity_tsum (fun n => show Measurable
        (fun x : ℝ => ENNReal.ofReal (primeWeight n (-x))) from
          ((continuous_primeWeight n).comp continuous_neg).measurable.ennreal_ofReal),
      tsum_ofReal_primeWeight_neg] at hi
    exact (integrable_weighted_iff volume hmeasR
      (Eventually.of_forall fun x => tsum_nonneg fun n => primeWeight_nonneg n (-x)) _).mp hi
  rw [integral_add (integrable_allPrime_left_sq u) (integrable_allPrime_right_sq u),
    hL, hR, ← integral_add hintL hintR, inner_primeDiagonalOperator_self_eq_volume]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← add_mul, ← (summable_primeWeight x).tsum_add (summable_primeWeight (-x)),
    tsum_primeWeight_add_neg x]

/-- **Exact Edge-Measure Integral Formula for `primeShiftOperator`**:
for every `u : MassSpace`,
`⟪primeShiftOperator u, u⟫_ℝ = 2 * ∫ e, u (left e) * u (right e) ∂allPrimeMeasure`. -/
theorem inner_primeShiftOperator_self_eq_integral (u : MassSpace) :
    ⟪primeShiftOperator u, u⟫_ℝ =
      2 * ∫ e, u (left e) * u (right e) ∂allPrimeMeasure := by
  have hint_sum : Integrable (fun e => u (left e) ^ 2 + u (right e) ^ 2) allPrimeMeasure :=
    (integrable_allPrime_left_sq u).add (integrable_allPrime_right_sq u)
  have hint_diff : Integrable (fun e => difference u e ^ 2) allPrimeMeasure :=
    (memLp_allPrime_difference (Lp.memLp u)).integrable_sq
  change ⟪primeDiagonalOperator u - primeGenerator u, u⟫_ℝ = _
  rw [inner_sub_left, ← integral_allPrime_left_sq_add_right_sq u, inner_primeGenerator_eq_integral]
  simp only [← pow_two]
  rw [← integral_sub hint_sum hint_diff, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with e
  change (u (left e) ^ 2 + u (right e) ^ 2) - (u (left e) - u (right e)) ^ 2 =
    2 * (u (left e) * u (right e))
  ring

/-- The quadratic form of `primeShiftOperator` is bounded in absolute value by the quadratic form
of `primeDiagonalOperator`. -/
theorem abs_inner_primeShiftOperator_self_le (u : MassSpace) :
    |⟪primeShiftOperator u, u⟫_ℝ| ≤ ⟪primeDiagonalOperator u, u⟫_ℝ := by
  rw [abs_le]
  have hminus : 0 ≤ ⟪primeDiagonalOperator u, u⟫_ℝ - ⟪primeShiftOperator u, u⟫_ℝ := by
    have h : ⟪primeDiagonalOperator u, u⟫_ℝ - ⟪primeShiftOperator u, u⟫_ℝ =
        ⟪primeGenerator u, u⟫_ℝ := by
      change ⟪primeDiagonalOperator u, u⟫_ℝ -
        ⟪primeDiagonalOperator u - primeGenerator u, u⟫_ℝ = _
      rw [inner_sub_left]
      ring
    rw [h, inner_primeGenerator_self]
    positivity
  have hplus : 0 ≤ ⟪primeDiagonalOperator u, u⟫_ℝ + ⟪primeShiftOperator u, u⟫_ℝ := by
    have hint_sum : Integrable (fun e => u (left e) ^ 2 + u (right e) ^ 2) allPrimeMeasure :=
      (integrable_allPrime_left_sq u).add (integrable_allPrime_right_sq u)
    have hint_cross : Integrable (fun e => 2 * (u (left e) * u (right e))) allPrimeMeasure :=
      (integrable_allPrime_left_mul_right u u).const_mul 2
    rw [← integral_allPrime_left_sq_add_right_sq u, inner_primeShiftOperator_self_eq_integral,
      ← integral_const_mul, ← integral_add hint_sum hint_cross]
    refine integral_nonneg fun e => ?_
    change 0 ≤ (u (left e) ^ 2 + u (right e) ^ 2) + 2 * (u (left e) * u (right e))
    have : (u (left e) ^ 2 + u (right e) ^ 2) + 2 * (u (left e) * u (right e)) =
        (u (left e) + u (right e)) ^ 2 := by ring
    rw [this]
    exact sq_nonneg _
  constructor <;> linarith

end RHTower.CHMDPolar
