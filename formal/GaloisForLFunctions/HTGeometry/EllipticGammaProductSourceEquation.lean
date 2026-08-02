import GaloisForLFunctions.HTGeometry.EllipticGammaProduct
import GaloisForLFunctions.HTGeometry.EllipticGammaAdditiveLogKernel

/-!
# Multiplicative source equations for the elliptic-gamma product

The period-one product identity and both structural-period source equations are proved exactly.
The two-dimensional products are split into a zero face and successor face through explicit
equivalences.  This avoids a Fubini conversion and preserves unconditional-product semantics even
when a factor vanishes.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-! ## First structural period -/

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

def ellipticGammaMultiplicativeThetaBoundary (tau z : ℂ) : ℂ :=
  (∏' k : ℕ, ellipticGammaForwardBoundaryFactor tau k z) *
    ∏' k : ℕ, ellipticGammaBackwardBoundaryFactor tau k z

/-! ## Second structural period -/

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

def ellipticGammaMultiplicativeThetaBoundaryTau (sigma tau z : ℂ) : ℂ :=
  (∏' j : ℕ, ellipticGammaTauForwardBoundaryFactor sigma tau j z) *
    ∏' j : ℕ, ellipticGammaTauBackwardBoundaryFactor sigma tau j z

/-! ## Unconditional product reindexing -/

/-- Split the zero face from the successor face of `ℕ × α`. -/
private def natProdZeroSuccEquiv (α : Type*) : α ⊕ (ℕ × α) ≃ ℕ × α where
  toFun
    | Sum.inl a => (0, a)
    | Sum.inr (n, a) => (n + 1, a)
  invFun
    | (0, a) => Sum.inl a
    | (n + 1, a) => Sum.inr (n, a)
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨_ | n, a⟩ <;> rfl

/-- Split the zero face from the successor face of `α × ℕ`. -/
private def prodNatZeroSuccEquiv (α : Type*) : α ⊕ (α × ℕ) ≃ α × ℕ where
  toFun
    | Sum.inl a => (a, 0)
    | Sum.inr (a, n) => (a, n + 1)
  invFun
    | (a, 0) => Sum.inl a
    | (a, n + 1) => Sum.inr (a, n)
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨a, _ | n⟩ <;> rfl

private theorem complex_tprod_natProd_eq_zero_mul_succ
    (f : ℕ × ℕ → ℂ)
    (hzero : Multipliable (fun a : ℕ => f (0, a)))
    (hsucc : Multipliable (fun p : ℕ × ℕ => f (p.1 + 1, p.2))) :
    (∏' p : ℕ × ℕ, f p) =
      (∏' a : ℕ, f (0, a)) * ∏' p : ℕ × ℕ, f (p.1 + 1, p.2) := by
  let e := natProdZeroSuccEquiv ℕ
  calc
    (∏' p : ℕ × ℕ, f p) = ∏' s : ℕ ⊕ (ℕ × ℕ), f (e s) :=
      (e.tprod_eq f).symm
    _ = (∏' a : ℕ, f (0, a)) * ∏' p : ℕ × ℕ, f (p.1 + 1, p.2) := by
      exact hzero.tprod_sum hsucc

private theorem complex_tprod_prodNat_eq_zero_mul_succ
    (f : ℕ × ℕ → ℂ)
    (hzero : Multipliable (fun a : ℕ => f (a, 0)))
    (hsucc : Multipliable (fun p : ℕ × ℕ => f (p.1, p.2 + 1))) :
    (∏' p : ℕ × ℕ, f p) =
      (∏' a : ℕ, f (a, 0)) * ∏' p : ℕ × ℕ, f (p.1, p.2 + 1) := by
  let e := prodNatZeroSuccEquiv ℕ
  calc
    (∏' p : ℕ × ℕ, f p) = ∏' s : ℕ ⊕ (ℕ × ℕ), f (e s) :=
      (e.tprod_eq f).symm
    _ = (∏' a : ℕ, f (a, 0)) * ∏' p : ℕ × ℕ, f (p.1, p.2 + 1) := by
      exact hzero.tprod_sum hsucc

private theorem multipliable_forwardBoundaryAux
    {q x : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun k : ℕ => 1 - q ^ (k + 1) / x) := by
  have hs : Summable (fun k : ℕ => -(q ^ (k + 1) / x)) := by
    apply ((summable_geometric_of_norm_lt_one hq).mul_left (-q * x⁻¹)).congr
    intro k
    simp only [div_eq_mul_inv, pow_succ]
    ring
  simpa only [sub_eq_add_neg] using
    Complex.multipliable_one_add_of_summable hs

private theorem multipliable_backwardBoundaryAux
    {q x : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun k : ℕ => 1 - q ^ k * x) := by
  have hs : Summable (fun k : ℕ => -(q ^ k * x)) := by
    exact ((summable_geometric_of_norm_lt_one hq).mul_right (-x)).congr fun k => by ring
  simpa only [sub_eq_add_neg] using
    Complex.multipliable_one_add_of_summable hs

theorem multipliable_ellipticGammaForwardBoundaryFactor
    {tau z : ℂ} (htau : 0 < tau.im) :
    Multipliable (fun k : ℕ => ellipticGammaForwardBoundaryFactor tau k z) := by
  simpa only [ellipticGammaForwardBoundaryFactor] using
    multipliable_forwardBoundaryAux
      (q := ellipticNome tau) (x := ellipticThetaCoordinate tau z)
      (norm_ellipticNome_lt_one htau)

theorem multipliable_ellipticGammaBackwardBoundaryFactor
    {tau z : ℂ} (htau : 0 < tau.im) :
    Multipliable (fun k : ℕ => ellipticGammaBackwardBoundaryFactor tau k z) := by
  simpa only [ellipticGammaBackwardBoundaryFactor] using
    multipliable_backwardBoundaryAux
      (q := ellipticNome tau) (x := ellipticThetaCoordinate tau z)
      (norm_ellipticNome_lt_one htau)

/-! ## Whole-product structural-period laws -/

set_option maxHeartbeats 600000 in
theorem ellipticGammaForwardProduct_add_sigma
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ) :
    ellipticGammaForwardProduct sigma tau (z + sigma) =
      (∏' k : ℕ, ellipticGammaForwardBoundaryFactor tau k z) *
        ellipticGammaForwardProduct sigma tau z := by
  have hunshift : Multipliable
      (fun jk : ℕ × ℕ => ellipticGammaForwardFactor sigma tau jk z) :=
    ((hasProdLocallyUniformlyOn_ellipticGammaForwardFactor hsigma htau).hasProd
      (Set.mem_univ z)).multipliable
  have hzeroMult : Multipliable (fun k : ℕ =>
      ellipticGammaForwardFactor sigma tau (0, k) (z + sigma)) :=
    (multipliable_ellipticGammaForwardBoundaryFactor htau).congr fun k =>
      (ellipticGammaForwardFactor_add_sigma_zero sigma tau z k).symm
  have hsuccMult : Multipliable (fun p : ℕ × ℕ =>
      ellipticGammaForwardFactor sigma tau (p.1 + 1, p.2) (z + sigma)) :=
    hunshift.congr fun p =>
      (ellipticGammaForwardFactor_add_sigma_succ sigma tau z p.1 p.2).symm
  have hzero :
      (∏' k : ℕ, ellipticGammaForwardFactor sigma tau (0, k) (z + sigma)) =
        ∏' k : ℕ, ellipticGammaForwardBoundaryFactor tau k z := by
    apply tprod_congr
    exact ellipticGammaForwardFactor_add_sigma_zero sigma tau z
  have hsucc :
      (∏' p : ℕ × ℕ,
        ellipticGammaForwardFactor sigma tau (p.1 + 1, p.2) (z + sigma)) =
        ellipticGammaForwardProduct sigma tau z := by
    rw [ellipticGammaForwardProduct]
    apply tprod_congr
    rintro ⟨j, k⟩
    exact ellipticGammaForwardFactor_add_sigma_succ sigma tau z j k
  change (∏' p : ℕ × ℕ,
      ellipticGammaForwardFactor sigma tau p (z + sigma)) = _
  exact (complex_tprod_natProd_eq_zero_mul_succ _ hzeroMult hsuccMult).trans
    (congrArg₂ (· * ·) hzero hsucc)

set_option maxHeartbeats 600000 in
theorem ellipticGammaBackwardProduct_eq_boundary_mul_add_sigma
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ) :
    ellipticGammaBackwardProduct sigma tau z =
      (∏' k : ℕ, ellipticGammaBackwardBoundaryFactor tau k z) *
        ellipticGammaBackwardProduct sigma tau (z + sigma) := by
  have hshift : Multipliable
      (fun jk : ℕ × ℕ => ellipticGammaBackwardFactor sigma tau jk (z + sigma)) :=
    ((hasProdLocallyUniformlyOn_ellipticGammaBackwardFactor hsigma htau).hasProd
      (Set.mem_univ (z + sigma))).multipliable
  have hzeroMult : Multipliable (fun k : ℕ =>
      ellipticGammaBackwardFactor sigma tau (0, k) z) :=
    (multipliable_ellipticGammaBackwardBoundaryFactor htau).congr fun k =>
      (ellipticGammaBackwardFactor_zero sigma tau z k).symm
  have hsuccMult : Multipliable (fun p : ℕ × ℕ =>
      ellipticGammaBackwardFactor sigma tau (p.1 + 1, p.2) z) :=
    hshift.congr fun p =>
      ellipticGammaBackwardFactor_add_sigma sigma tau z p.1 p.2
  have hzero :
      (∏' k : ℕ, ellipticGammaBackwardFactor sigma tau (0, k) z) =
        ∏' k : ℕ, ellipticGammaBackwardBoundaryFactor tau k z := by
    apply tprod_congr
    exact ellipticGammaBackwardFactor_zero sigma tau z
  have hsucc :
      (∏' p : ℕ × ℕ, ellipticGammaBackwardFactor sigma tau (p.1 + 1, p.2) z) =
        ellipticGammaBackwardProduct sigma tau (z + sigma) := by
    rw [ellipticGammaBackwardProduct]
    apply tprod_congr
    rintro ⟨j, k⟩
    exact (ellipticGammaBackwardFactor_add_sigma sigma tau z j k).symm
  change (∏' p : ℕ × ℕ, ellipticGammaBackwardFactor sigma tau p z) = _
  exact (complex_tprod_natProd_eq_zero_mul_succ _ hzeroMult hsuccMult).trans
    (congrArg₂ (· * ·) hzero hsucc)

set_option maxHeartbeats 600000 in
theorem ellipticGammaForwardProduct_add_tau
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ) :
    ellipticGammaForwardProduct sigma tau (z + tau) =
      (∏' j : ℕ, ellipticGammaTauForwardBoundaryFactor sigma tau j z) *
        ellipticGammaForwardProduct sigma tau z := by
  have hunshift : Multipliable
      (fun jk : ℕ × ℕ => ellipticGammaForwardFactor sigma tau jk z) :=
    ((hasProdLocallyUniformlyOn_ellipticGammaForwardFactor hsigma htau).hasProd
      (Set.mem_univ z)).multipliable
  have hzeroMult : Multipliable (fun j : ℕ =>
      ellipticGammaForwardFactor sigma tau (j, 0) (z + tau)) :=
    (multipliable_forwardBoundaryAux
      (q := ellipticNome sigma) (x := ellipticThetaCoordinate tau z)
      (norm_ellipticNome_lt_one hsigma)).congr fun j => by
        simpa only [ellipticGammaTauForwardBoundaryFactor] using
          (ellipticGammaForwardFactor_add_tau_zero sigma tau z j).symm
  have hsuccMult : Multipliable (fun p : ℕ × ℕ =>
      ellipticGammaForwardFactor sigma tau (p.1, p.2 + 1) (z + tau)) :=
    hunshift.congr fun p =>
      (ellipticGammaForwardFactor_add_tau_succ sigma tau z p.1 p.2).symm
  have hzero :
      (∏' j : ℕ, ellipticGammaForwardFactor sigma tau (j, 0) (z + tau)) =
        ∏' j : ℕ, ellipticGammaTauForwardBoundaryFactor sigma tau j z := by
    apply tprod_congr
    exact ellipticGammaForwardFactor_add_tau_zero sigma tau z
  have hsucc :
      (∏' p : ℕ × ℕ,
        ellipticGammaForwardFactor sigma tau (p.1, p.2 + 1) (z + tau)) =
        ellipticGammaForwardProduct sigma tau z := by
    rw [ellipticGammaForwardProduct]
    apply tprod_congr
    rintro ⟨j, k⟩
    exact ellipticGammaForwardFactor_add_tau_succ sigma tau z j k
  change (∏' p : ℕ × ℕ,
      ellipticGammaForwardFactor sigma tau p (z + tau)) = _
  exact (complex_tprod_prodNat_eq_zero_mul_succ _ hzeroMult hsuccMult).trans
    (congrArg₂ (· * ·) hzero hsucc)

set_option maxHeartbeats 600000 in
theorem ellipticGammaBackwardProduct_eq_boundary_mul_add_tau
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ) :
    ellipticGammaBackwardProduct sigma tau z =
      (∏' j : ℕ, ellipticGammaTauBackwardBoundaryFactor sigma tau j z) *
        ellipticGammaBackwardProduct sigma tau (z + tau) := by
  have hshift : Multipliable
      (fun jk : ℕ × ℕ => ellipticGammaBackwardFactor sigma tau jk (z + tau)) :=
    ((hasProdLocallyUniformlyOn_ellipticGammaBackwardFactor hsigma htau).hasProd
      (Set.mem_univ (z + tau))).multipliable
  have hzeroMult : Multipliable (fun j : ℕ =>
      ellipticGammaBackwardFactor sigma tau (j, 0) z) :=
    (multipliable_backwardBoundaryAux
      (q := ellipticNome sigma) (x := ellipticThetaCoordinate tau z)
      (norm_ellipticNome_lt_one hsigma)).congr fun j => by
        simpa only [ellipticGammaTauBackwardBoundaryFactor] using
          (ellipticGammaBackwardFactor_tau_zero sigma tau z j).symm
  have hsuccMult : Multipliable (fun p : ℕ × ℕ =>
      ellipticGammaBackwardFactor sigma tau (p.1, p.2 + 1) z) :=
    hshift.congr fun p =>
      ellipticGammaBackwardFactor_add_tau sigma tau z p.1 p.2
  have hzero :
      (∏' j : ℕ, ellipticGammaBackwardFactor sigma tau (j, 0) z) =
        ∏' j : ℕ, ellipticGammaTauBackwardBoundaryFactor sigma tau j z := by
    apply tprod_congr
    exact ellipticGammaBackwardFactor_tau_zero sigma tau z
  have hsucc :
      (∏' p : ℕ × ℕ, ellipticGammaBackwardFactor sigma tau (p.1, p.2 + 1) z) =
        ellipticGammaBackwardProduct sigma tau (z + tau) := by
    rw [ellipticGammaBackwardProduct]
    apply tprod_congr
    rintro ⟨j, k⟩
    exact (ellipticGammaBackwardFactor_add_tau sigma tau z j k).symm
  change (∏' p : ℕ × ℕ, ellipticGammaBackwardFactor sigma tau p z) = _
  exact (complex_tprod_prodNat_eq_zero_mul_succ _ hzeroMult hsuccMult).trans
    (congrArg₂ (· * ·) hzero hsucc)

/-- On the regular locus, the whole elliptic-gamma product satisfies its first structural-period
source equation. -/
theorem ellipticGammaProduct_add_sigma
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ)
    (hzB : ellipticGammaBackwardProduct sigma tau z ≠ 0) :
    ellipticGammaProduct sigma tau (z + sigma) =
      ellipticGammaMultiplicativeThetaBoundary tau z *
        ellipticGammaProduct sigma tau z := by
  have hB := ellipticGammaBackwardProduct_eq_boundary_mul_add_sigma hsigma htau z
  have hparts :
      (∏' k : ℕ, ellipticGammaBackwardBoundaryFactor tau k z) ≠ 0 ∧
        ellipticGammaBackwardProduct sigma tau (z + sigma) ≠ 0 := by
    rw [hB] at hzB
    exact mul_ne_zero_iff.mp hzB
  rw [ellipticGammaProduct, ellipticGammaProduct,
    ellipticGammaForwardProduct_add_sigma hsigma htau z,
    ellipticGammaMultiplicativeThetaBoundary, hB]
  field_simp [hparts.1, hparts.2]

/-- On the regular locus, the whole elliptic-gamma product satisfies its second
structural-period source equation. -/
theorem ellipticGammaProduct_add_tau
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) (z : ℂ)
    (hzB : ellipticGammaBackwardProduct sigma tau z ≠ 0) :
    ellipticGammaProduct sigma tau (z + tau) =
      ellipticGammaMultiplicativeThetaBoundaryTau sigma tau z *
        ellipticGammaProduct sigma tau z := by
  have hB := ellipticGammaBackwardProduct_eq_boundary_mul_add_tau hsigma htau z
  have hparts :
      (∏' j : ℕ, ellipticGammaTauBackwardBoundaryFactor sigma tau j z) ≠ 0 ∧
        ellipticGammaBackwardProduct sigma tau (z + tau) ≠ 0 := by
    rw [hB] at hzB
    exact mul_ne_zero_iff.mp hzB
  rw [ellipticGammaProduct, ellipticGammaProduct,
    ellipticGammaForwardProduct_add_tau hsigma htau z,
    ellipticGammaMultiplicativeThetaBoundaryTau, hB]
  field_simp [hparts.1, hparts.2]

/-! ## Exact period-one law -/

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

end

end GaloisForLFunctions
