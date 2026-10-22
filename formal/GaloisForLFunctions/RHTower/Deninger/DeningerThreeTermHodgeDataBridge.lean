/-
The concrete three-term Hodge purity is the abstract one.

`DeningerArithmeticThreeTermHodge.HodgeData` packages a transverse flow, a weight-one cup pairing
and a positive flow-natural anti-linear Hodge operator on an abstract space, and proves from them
that every eigenvalue of the flow has real part one half, together with the one-way spectral
comparison to the Riemann hypothesis.  `DeningerArithmeticThreeTermHodgePurity` carries the same
data concretely on the middle cohomology of a three-term arithmetic flow, and reproves the same two
statements; the two modules never met.

The concrete data is abstract Hodge data: the flow is `thetaH1`, the pairing is the descended
`pairH11`, the Hodge operator is `star`, and weight-one naturality is the descended middle weight
law.  So the concrete purity theorem and its spectral corollary are the abstract ones read on the
realization.
-/
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticThreeTermHodgePurity
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticThreeTermHodge
import GaloisForLFunctions.RHTower.XiSpectralSupportCriterion

namespace RHTower

noncomputable section

variable {A0 A1 A2 : Type*}
variable [AddCommGroup A0] [Module ℂ A0]
variable [AddCommGroup A1] [Module ℂ A1]
variable [AddCommGroup A2] [Module ℂ A2]

/-- **The concrete three-term Hodge package is abstract Hodge data on the middle cohomology.**
The transverse flow, the descended cup–trace pairing and the anti-linear star are the three
operators of `HodgeData`; weight-one naturality is the descended middle weight law. -/
def DeningerArithmeticThreeTermHodge.toHodgeData
    {F : DeningerArithmeticThreeTermFlow ℂ A0 A1 A2}
    {P : DeningerArithmeticThreeTermCupPairing F.complex}
    (Hodge : DeningerArithmeticThreeTermHodge F P)
    (W : DeningerArithmeticThreeTermWeightOneCup F P) :
    DeningerArithmeticThreeTermHodge.HodgeData F.complex.H1 where
  theta := F.thetaH1
  cup := P.pairH11 F.complex
  hodge := Hodge.star
  weightOne := fun x y =>
    DeningerArithmeticThreeTermWeightOneCup.middle_weight_on_cohomology F P W x y
  hodgeSq := Hodge.square_neg
  commutes := Hodge.theta_star
  positive := fun _ hx => Hodge.positive hx

/-- **Concrete three-term Hodge purity is the abstract purity theorem.**  Every genuine eigenvalue
of the middle flow has real part one half, derived from `HodgeData` rather than reproved. -/
theorem DeningerArithmeticThreeTermHodge.eigenvalue_re_eq_half_of_hodgeData
    {F : DeningerArithmeticThreeTermFlow ℂ A0 A1 A2}
    {P : DeningerArithmeticThreeTermCupPairing F.complex}
    (Hodge : DeningerArithmeticThreeTermHodge F P)
    (W : DeningerArithmeticThreeTermWeightOneCup F P)
    {rho : ℂ} {x : F.complex.H1} (hx0 : x ≠ 0)
    (hx : F.thetaH1 x = rho • x) :
    rho.re = 1 / 2 :=
  DeningerArithmeticThreeTermHodge.theta_eigenvalue_re_eq_half
    (Hodge.toHodgeData W) hx0 hx

/-- The centered coordinate form of the concrete purity statement. -/
theorem DeningerArithmeticThreeTermHodge.eigenvalue_eq_half_add_I_mul_of_hodgeData
    {F : DeningerArithmeticThreeTermFlow ℂ A0 A1 A2}
    {P : DeningerArithmeticThreeTermCupPairing F.complex}
    (Hodge : DeningerArithmeticThreeTermHodge F P)
    (W : DeningerArithmeticThreeTermWeightOneCup F P)
    {rho : ℂ} {x : F.complex.H1} (hx0 : x ≠ 0)
    (hx : F.thetaH1 x = rho • x) :
    rho = 1 / 2 + Complex.I * (rho.im : ℂ) :=
  DeningerArithmeticThreeTermHodge.eigenvalue_eq_half_add_I_mul
    (Hodge.toHodgeData W) hx0 hx

/-- **The one-way spectral comparison, on the concrete package.**  If every nontrivial zeta zero is
an eigenvalue of the middle flow, the Riemann hypothesis follows — the abstract corollary read
through the realization. -/
theorem DeningerArithmeticThreeTermHodge.riemannHypothesis_of_zetaZero_eigenvector_of_hodgeData
    {F : DeningerArithmeticThreeTermFlow ℂ A0 A1 A2}
    {P : DeningerArithmeticThreeTermCupPairing F.complex}
    (Hodge : DeningerArithmeticThreeTermHodge F P)
    (W : DeningerArithmeticThreeTermWeightOneCup F P)
    (hspec : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
      ∃ x : F.complex.H1, x ≠ 0 ∧ F.thetaH1 x = s • x) :
    RiemannHypothesis :=
  DeningerArithmeticThreeTermHodge.riemannHypothesis_of_zetaZero_eigenvector
    (Hodge.toHodgeData W) hspec

/-- **The concrete spectral corollary, assembled from the two reusable pieces.**  Purity comes from
the abstract `HodgeData` argument and the passage to the critical line from the divisor-indexed
spectral criterion, so neither is repeated here. -/
theorem DeningerArithmeticThreeTermHodge.riemannHypothesis_of_xiPointSpectrum
    {F : DeningerArithmeticThreeTermFlow ℂ A0 A1 A2}
    {P : DeningerArithmeticThreeTermCupPairing F.complex}
    (Hodge : DeningerArithmeticThreeTermHodge F P)
    (W : DeningerArithmeticThreeTermWeightOneCup F P)
    (Spectrum : DeningerArithmeticThreeTermHodge.XiPointSpectrum F) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_centeredEigenvalue_re_eq_half fun ρ => ?_
  obtain ⟨x, hx0, hx⟩ := Spectrum.eigenvector ρ
  exact Hodge.eigenvalue_re_eq_half_of_hodgeData W hx0 hx

end

end RHTower
