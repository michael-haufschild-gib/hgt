import GaloisForLFunctions.HTGeometry.EllipticGammaProduct
import GaloisForLFunctions.HTGeometry.EllipticGammaAdditiveLogKernel

/-!
# Explicit multiplicative source equations for the elliptic-gamma product

Reindexing the convergent double products under either structural period peels off an explicit
one-dimensional theta boundary.  The resulting equations construct the three source ratios
directly from the period parameters: period one has ratio one, while the other two ratios are
one-dimensional products.  No elliptic-gamma germ is used to define those boundary products.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

def ellipticGammaForwardBoundaryFactor (tau : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  1 - ellipticNome tau ^ (k + 1) / ellipticThetaCoordinate tau z

theorem ellipticGammaForwardFactor_add_sigma_zero
    (sigma tau z : ℂ) (k : ℕ) :
    ellipticGammaForwardFactor sigma tau (0, k) (z + sigma) =
      ellipticGammaForwardBoundaryFactor tau k z := by
  rw [ellipticGammaForwardFactor, ellipticGammaForwardBoundaryFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaForwardArgument_mul_p_zero
    (ellipticNome_ne_zero sigma) (ellipticThetaCoordinate_ne_zero tau z)]

theorem ellipticGammaForwardFactor_add_sigma_succ
    (sigma tau z : ℂ) (j k : ℕ) :
    ellipticGammaForwardFactor sigma tau (j + 1, k) (z + sigma) =
      ellipticGammaForwardFactor sigma tau (j, k) z := by
  rw [ellipticGammaForwardFactor, ellipticGammaForwardFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaForwardArgument_mul_p_succ
    (ellipticNome_ne_zero sigma) (ellipticThetaCoordinate_ne_zero tau z)]

theorem ellipticGammaForwardProduct_add_sigma
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ) :
    ellipticGammaForwardProduct sigma tau (z + sigma) =
      (∏' k : ℕ, ellipticGammaForwardBoundaryFactor tau k z) *
        ellipticGammaForwardProduct sigma tau z := by
  let fs : ℕ × ℕ → ℂ := fun jk ↦
    ellipticGammaForwardFactor sigma tau jk (z + sigma)
  let f : ℕ × ℕ → ℂ := fun jk ↦
    ellipticGammaForwardFactor sigma tau jk z
  have hfs : Multipliable fs :=
    ((hasProdLocallyUniformlyOn_ellipticGammaForwardFactor hsigma htau).hasProd
      (Set.mem_univ (z + sigma))).multipliable
  have hf : Multipliable f :=
    ((hasProdLocallyUniformlyOn_ellipticGammaForwardFactor hsigma htau).hasProd
      (Set.mem_univ z)).multipliable
  rw [ellipticGammaForwardProduct, ellipticGammaForwardProduct,
    hfs.tprod_prod, hf.tprod_prod]
  rw [(hfs.prod).tprod_eq_zero_mul]
  congr 1
  · apply tprod_congr
    intro k
    exact ellipticGammaForwardFactor_add_sigma_zero sigma tau z k
  · apply tprod_congr
    intro j
    apply tprod_congr
    intro k
    exact ellipticGammaForwardFactor_add_sigma_succ sigma tau z j k

def ellipticGammaBackwardBoundaryFactor (tau : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  1 - ellipticNome tau ^ k * ellipticThetaCoordinate tau z

theorem ellipticGammaBackwardFactor_zero
    (sigma tau z : ℂ) (k : ℕ) :
    ellipticGammaBackwardFactor sigma tau (0, k) z =
      ellipticGammaBackwardBoundaryFactor tau k z := by
  simp [ellipticGammaBackwardFactor, ellipticGammaBackwardBoundaryFactor,
    ellipticGammaBackwardArgument]

theorem ellipticGammaBackwardFactor_add_sigma
    (sigma tau z : ℂ) (j k : ℕ) :
    ellipticGammaBackwardFactor sigma tau (j, k) (z + sigma) =
      ellipticGammaBackwardFactor sigma tau (j + 1, k) z := by
  rw [ellipticGammaBackwardFactor, ellipticGammaBackwardFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaBackwardArgument_mul_p]

theorem ellipticGammaBackwardProduct_eq_boundary_mul_add_sigma
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ) :
    ellipticGammaBackwardProduct sigma tau z =
      (∏' k : ℕ, ellipticGammaBackwardBoundaryFactor tau k z) *
        ellipticGammaBackwardProduct sigma tau (z + sigma) := by
  let f : ℕ × ℕ → ℂ := fun jk ↦
    ellipticGammaBackwardFactor sigma tau jk z
  let fs : ℕ × ℕ → ℂ := fun jk ↦
    ellipticGammaBackwardFactor sigma tau jk (z + sigma)
  have hf : Multipliable f :=
    ((hasProdLocallyUniformlyOn_ellipticGammaBackwardFactor hsigma htau).hasProd
      (Set.mem_univ z)).multipliable
  have hfs : Multipliable fs :=
    ((hasProdLocallyUniformlyOn_ellipticGammaBackwardFactor hsigma htau).hasProd
      (Set.mem_univ (z + sigma))).multipliable
  rw [ellipticGammaBackwardProduct, ellipticGammaBackwardProduct,
    hf.tprod_prod, hfs.tprod_prod]
  rw [(hf.prod).tprod_eq_zero_mul]
  congr 1
  · apply tprod_congr
    intro k
    exact ellipticGammaBackwardFactor_zero sigma tau z k
  · apply tprod_congr
    intro j
    apply tprod_congr
    intro k
    exact (ellipticGammaBackwardFactor_add_sigma sigma tau z j k).symm

def ellipticGammaMultiplicativeThetaBoundary (tau z : ℂ) : ℂ :=
  (∏' k : ℕ, ellipticGammaForwardBoundaryFactor tau k z) *
    ∏' k : ℕ, ellipticGammaBackwardBoundaryFactor tau k z

theorem ellipticGammaProduct_add_sigma
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ)
    (hzB : ellipticGammaBackwardProduct sigma tau z ≠ 0)
    (hzsB : ellipticGammaBackwardProduct sigma tau (z + sigma) ≠ 0) :
    ellipticGammaProduct sigma tau (z + sigma) =
      ellipticGammaMultiplicativeThetaBoundary tau z *
        ellipticGammaProduct sigma tau z := by
  let A : ℂ := ∏' k : ℕ, ellipticGammaForwardBoundaryFactor tau k z
  let C : ℂ := ∏' k : ℕ, ellipticGammaBackwardBoundaryFactor tau k z
  have hF := ellipticGammaForwardProduct_add_sigma hsigma htau z
  have hB := ellipticGammaBackwardProduct_eq_boundary_mul_add_sigma hsigma htau z
  have hC : C ≠ 0 := by
    intro hzero
    apply hzB
    simpa [C, hzero] using hB
  rw [ellipticGammaProduct, ellipticGammaProduct,
    ellipticGammaMultiplicativeThetaBoundary]
  change ellipticGammaForwardProduct sigma tau (z + sigma) /
      ellipticGammaBackwardProduct sigma tau (z + sigma) =
    A * C * (ellipticGammaForwardProduct sigma tau z /
      ellipticGammaBackwardProduct sigma tau z)
  rw [hF, hB]
  field_simp [hC, hzsB]
  ring

def ellipticGammaTauForwardBoundaryFactor (sigma tau : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  1 - ellipticNome sigma ^ (j + 1) / ellipticThetaCoordinate tau z

def ellipticGammaTauBackwardBoundaryFactor (sigma tau : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  1 - ellipticNome sigma ^ j * ellipticThetaCoordinate tau z

theorem ellipticGammaForwardFactor_add_tau_zero
    (sigma tau z : ℂ) (j : ℕ) :
    ellipticGammaForwardFactor sigma tau (j, 0) (z + tau) =
      ellipticGammaTauForwardBoundaryFactor sigma tau j z := by
  rw [ellipticGammaForwardFactor, ellipticGammaTauForwardBoundaryFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaForwardArgument_mul_q_zero
    (ellipticNome_ne_zero tau) (ellipticThetaCoordinate_ne_zero tau z)]

theorem ellipticGammaForwardFactor_add_tau_succ
    (sigma tau z : ℂ) (j k : ℕ) :
    ellipticGammaForwardFactor sigma tau (j, k + 1) (z + tau) =
      ellipticGammaForwardFactor sigma tau (j, k) z := by
  rw [ellipticGammaForwardFactor, ellipticGammaForwardFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaForwardArgument_mul_q_succ
    (ellipticNome_ne_zero tau) (ellipticThetaCoordinate_ne_zero tau z)]

theorem ellipticGammaForwardProduct_add_tau
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ) :
    ellipticGammaForwardProduct sigma tau (z + tau) =
      (∏' j : ℕ, ellipticGammaTauForwardBoundaryFactor sigma tau j z) *
        ellipticGammaForwardProduct sigma tau z := by
  let fs : ℕ × ℕ → ℂ := fun jk ↦
    ellipticGammaForwardFactor sigma tau jk (z + tau)
  let f : ℕ × ℕ → ℂ := fun jk ↦
    ellipticGammaForwardFactor sigma tau jk z
  have hfs : Multipliable fs :=
    ((hasProdLocallyUniformlyOn_ellipticGammaForwardFactor hsigma htau).hasProd
      (Set.mem_univ (z + tau))).multipliable
  have hf : Multipliable f :=
    ((hasProdLocallyUniformlyOn_ellipticGammaForwardFactor hsigma htau).hasProd
      (Set.mem_univ z)).multipliable
  rw [ellipticGammaForwardProduct, ellipticGammaForwardProduct,
    hfs.tprod_prod, hf.tprod_prod, ← hfs.tprod_comm, ← hf.tprod_comm]
  rw [(hfs.prod_symm.prod).tprod_eq_zero_mul]
  congr 1
  · apply tprod_congr
    intro j
    exact ellipticGammaForwardFactor_add_tau_zero sigma tau z j
  · apply tprod_congr
    intro k
    apply tprod_congr
    intro j
    exact ellipticGammaForwardFactor_add_tau_succ sigma tau z j k

theorem ellipticGammaBackwardFactor_add_tau
    (sigma tau z : ℂ) (j k : ℕ) :
    ellipticGammaBackwardFactor sigma tau (j, k) (z + tau) =
      ellipticGammaBackwardFactor sigma tau (j, k + 1) z := by
  rw [ellipticGammaBackwardFactor, ellipticGammaBackwardFactor,
    ellipticThetaCoordinate_add]
  rw [ellipticGammaBackwardArgument_mul_q]

theorem ellipticGammaBackwardFactor_tau_zero
    (sigma tau z : ℂ) (j : ℕ) :
    ellipticGammaBackwardFactor sigma tau (j, 0) z =
      ellipticGammaTauBackwardBoundaryFactor sigma tau j z := by
  simp [ellipticGammaBackwardFactor, ellipticGammaTauBackwardBoundaryFactor,
    ellipticGammaBackwardArgument]

theorem ellipticGammaBackwardProduct_eq_boundary_mul_add_tau
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ) :
    ellipticGammaBackwardProduct sigma tau z =
      (∏' j : ℕ, ellipticGammaTauBackwardBoundaryFactor sigma tau j z) *
        ellipticGammaBackwardProduct sigma tau (z + tau) := by
  let f : ℕ × ℕ → ℂ := fun jk ↦
    ellipticGammaBackwardFactor sigma tau jk z
  let fs : ℕ × ℕ → ℂ := fun jk ↦
    ellipticGammaBackwardFactor sigma tau jk (z + tau)
  have hf : Multipliable f :=
    ((hasProdLocallyUniformlyOn_ellipticGammaBackwardFactor hsigma htau).hasProd
      (Set.mem_univ z)).multipliable
  have hfs : Multipliable fs :=
    ((hasProdLocallyUniformlyOn_ellipticGammaBackwardFactor hsigma htau).hasProd
      (Set.mem_univ (z + tau))).multipliable
  rw [ellipticGammaBackwardProduct, ellipticGammaBackwardProduct,
    hf.tprod_prod, hfs.tprod_prod, ← hf.tprod_comm, ← hfs.tprod_comm]
  rw [(hf.prod_symm.prod).tprod_eq_zero_mul]
  congr 1
  · apply tprod_congr
    intro j
    exact ellipticGammaBackwardFactor_tau_zero sigma tau z j
  · apply tprod_congr
    intro k
    apply tprod_congr
    intro j
    exact (ellipticGammaBackwardFactor_add_tau sigma tau z j k).symm

def ellipticGammaMultiplicativeThetaBoundaryTau (sigma tau z : ℂ) : ℂ :=
  (∏' j : ℕ, ellipticGammaTauForwardBoundaryFactor sigma tau j z) *
    ∏' j : ℕ, ellipticGammaTauBackwardBoundaryFactor sigma tau j z

theorem ellipticGammaProduct_add_tau
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ)
    (hzB : ellipticGammaBackwardProduct sigma tau z ≠ 0)
    (hztB : ellipticGammaBackwardProduct sigma tau (z + tau) ≠ 0) :
    ellipticGammaProduct sigma tau (z + tau) =
      ellipticGammaMultiplicativeThetaBoundaryTau sigma tau z *
        ellipticGammaProduct sigma tau z := by
  let A : ℂ := ∏' j : ℕ, ellipticGammaTauForwardBoundaryFactor sigma tau j z
  let C : ℂ := ∏' j : ℕ, ellipticGammaTauBackwardBoundaryFactor sigma tau j z
  have hF := ellipticGammaForwardProduct_add_tau hsigma htau z
  have hB := ellipticGammaBackwardProduct_eq_boundary_mul_add_tau hsigma htau z
  have hC : C ≠ 0 := by
    intro hzero
    apply hzB
    simpa [C, hzero] using hB
  rw [ellipticGammaProduct, ellipticGammaProduct,
    ellipticGammaMultiplicativeThetaBoundaryTau]
  change ellipticGammaForwardProduct sigma tau (z + tau) /
      ellipticGammaBackwardProduct sigma tau (z + tau) =
    A * C * (ellipticGammaForwardProduct sigma tau z /
      ellipticGammaBackwardProduct sigma tau z)
  rw [hF, hB]
  field_simp [hC, hztB]
  ring

theorem ellipticGammaForwardProduct_add_one (sigma tau z : ℂ) :
    ellipticGammaForwardProduct sigma tau (z + 1) =
      ellipticGammaForwardProduct sigma tau z := by
  rw [ellipticGammaForwardProduct, ellipticGammaForwardProduct]
  apply tprod_congr
  intro jk
  rw [ellipticGammaForwardFactor, ellipticGammaForwardFactor,
    ellipticThetaCoordinate_add_one]

theorem ellipticGammaBackwardProduct_add_one (sigma tau z : ℂ) :
    ellipticGammaBackwardProduct sigma tau (z + 1) =
      ellipticGammaBackwardProduct sigma tau z := by
  rw [ellipticGammaBackwardProduct, ellipticGammaBackwardProduct]
  apply tprod_congr
  intro jk
  rw [ellipticGammaBackwardFactor, ellipticGammaBackwardFactor,
    ellipticThetaCoordinate_add_one]

theorem ellipticGammaProduct_add_one (sigma tau z : ℂ) :
    ellipticGammaProduct sigma tau (z + 1) =
      ellipticGammaProduct sigma tau z := by
  rw [ellipticGammaProduct, ellipticGammaProduct,
    ellipticGammaForwardProduct_add_one,
    ellipticGammaBackwardProduct_add_one]

/-- The explicit three-component multiplicative source boundary, constructed only from the two
period parameters and one-dimensional products. -/
def ellipticGammaExplicitSourceBoundary (sigma tau z : ℂ) : Fin 3 → ℂ :=
  ![1, ellipticGammaMultiplicativeThetaBoundary tau z,
    ellipticGammaMultiplicativeThetaBoundaryTau sigma tau z]

/-- The genuine elliptic-gamma product satisfies the explicit three source equations on the
common regular locus. -/
theorem ellipticGammaProduct_explicit_source_equations
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ)
    (hzB : ellipticGammaBackwardProduct sigma tau z ≠ 0)
    (hzsB : ellipticGammaBackwardProduct sigma tau (z + sigma) ≠ 0)
    (hztB : ellipticGammaBackwardProduct sigma tau (z + tau) ≠ 0) :
    ellipticGammaProduct sigma tau (z + 1) =
        ellipticGammaExplicitSourceBoundary sigma tau z 0 *
          ellipticGammaProduct sigma tau z ∧
      ellipticGammaProduct sigma tau (z + sigma) =
        ellipticGammaExplicitSourceBoundary sigma tau z 1 *
          ellipticGammaProduct sigma tau z ∧
      ellipticGammaProduct sigma tau (z + tau) =
        ellipticGammaExplicitSourceBoundary sigma tau z 2 *
          ellipticGammaProduct sigma tau z := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [ellipticGammaExplicitSourceBoundary] using
      ellipticGammaProduct_add_one sigma tau z
  · simpa [ellipticGammaExplicitSourceBoundary] using
      ellipticGammaProduct_add_sigma hsigma htau z hzB hzsB
  · simpa [ellipticGammaExplicitSourceBoundary] using
      ellipticGammaProduct_add_tau hsigma htau z hzB hztB

end

end GaloisForLFunctions
