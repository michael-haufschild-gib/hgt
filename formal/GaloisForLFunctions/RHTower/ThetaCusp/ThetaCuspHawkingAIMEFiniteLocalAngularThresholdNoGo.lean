import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMECrossBranchTeukolskyResidue
import GaloisForLFunctions.RHTower.FZZCigarPunctureFiniteDimensionalBarePencilNoGo
import GaloisForLFunctions.Bottcher.MonodromyObstruction

/-!
# HB finite-local-angular threshold no-go

After regular peripheral transients decay, the surviving source-adapted HB escape route is a
zero-frequency atom with the odd cubic AIME phase charge.  A finite-order local angular law acts
polynomially in the separated Teukolsky angular eigenvalue `Q`.  This file tests the full class at
once, without fixing the polynomial degree.

On the positive real Hardy line, `Im Q(t) = t / 4`, so distinct Hardy zeros give distinct angular
eigenvalues.  Exact AIME cancellation would make `(X + 2) * P - 12` vanish at every such value.
Hardy's theorem supplies a packet larger than its degree, forcing the polynomial to vanish
identically; evaluation at `X = -2` gives the contradiction `-12 = 0`.

Thus no finite-order local angular threshold operator can supply the remaining HB radiative `++`
extinction law on all unconditional Hardy-line Xi fibres.  The sharp survivor must contain the
nonlocal angular resolvent `(Q + 2)⁻¹`, genuinely infinite angular order, or fibre-adaptive data.

`[NEW] [HB] [AIME] [FINITE LOCAL ANGULAR] [ALL-DEGREES NO-GO] [ROUTE KILL] [LEAN-PROVED]`
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- Exact imaginary angular-eigenvalue coordinate on the real Hardy line. -/
lemma d4ThetaTeukolskyAngularQ_ofReal_im (t : ℝ) :
    (d4ThetaTeukolskyAngularQ (t : ℂ)).im = t / 4 := by
  rw [d4ThetaTeukolskyAngularQ_eq_rho]
  unfold d4ThetaTeukolskyRho
  norm_num
  ring

/-- The continued angular eigenvalue retains every real Hardy ordinate. -/
lemma d4ThetaTeukolskyAngularQ_ofReal_injective :
    Function.Injective (fun t : ℝ => d4ThetaTeukolskyAngularQ (t : ℂ)) := by
  intro s t h
  have him := congrArg Complex.im h
  rw [d4ThetaTeukolskyAngularQ_ofReal_im, d4ThetaTeukolskyAngularQ_ofReal_im] at him
  linarith

/-- The physical AIME angular denominator is regular at every positive real Hardy ordinate. -/
lemma d4ThetaTeukolskyAngularQ_ofReal_add_two_ne_zero {t : ℝ} (ht : 0 < t) :
    d4ThetaTeukolskyAngularQ (t : ℂ) + 2 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  norm_num [d4ThetaTeukolskyAngularQ_ofReal_im] at him
  linarith

/-- Coefficient produced by one finite-order local angular threshold operator.  On a separated
angular mode, every polynomial in the angular operator evaluates polynomially in `Q`. -/
def d4HBFiniteLocalAngularThresholdCoefficient (P : ℂ[X]) (z : ℂ) : ℂ :=
  P.eval (d4ThetaTeukolskyAngularQ z)

/-- Full AIME mass-jet coefficient after adding a finite-order local angular threshold law. -/
def d4HBFiniteLocalAngularThresholdFullCoefficient (P : ℂ[X]) (z : ℂ) : ℂ :=
  d4FundamentalQNMCrossBranchChiralMassJetNumerator z +
    d4HBFiniteLocalAngularThresholdCoefficient P z

/-- Proposed universal cancellation by one finite-order local angular threshold law. -/
def D4HBFiniteLocalAngularThresholdXiComplete (P : ℂ[X]) : Prop :=
  ∀ t : ℝ, 0 < t → XiC (t : ℂ) = 0 →
    d4HBFiniteLocalAngularThresholdFullCoefficient P (t : ℂ) = 0

/-- No polynomial angular response cancels the exact reciprocal AIME mass jet on every positive
real Hardy-line Xi fibre, regardless of polynomial degree. -/
theorem not_d4HBFiniteLocalAngularThresholdXiComplete (P : ℂ[X]) :
    ¬ D4HBFiniteLocalAngularThresholdXiComplete P := by
  intro hcomplete
  let R : ℂ[X] := (X + C 2) * P - C 12
  obtain ⟨E, hEpos, hEinj, hEzero⟩ :=
    exists_injective_positive_real_XiC_zero_packet (R.natDegree + 1)
  let q : Fin (R.natDegree + 1) → ℂ :=
    fun i => d4ThetaTeukolskyAngularQ (E i : ℂ)
  have hqinj : Function.Injective q := by
    exact d4ThetaTeukolskyAngularQ_ofReal_injective.comp hEinj
  let S : Finset ℂ := Finset.univ.image q
  have hScard : S.card = R.natDegree + 1 := by
    rw [show S = Finset.univ.image q from rfl]
    rw [Finset.card_image_of_injective _ hqinj]
    simp
  have hRroots : ∀ x ∈ S, R.eval x = 0 := by
    intro x hx
    rw [show S = Finset.univ.image q from rfl, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    have hcancel := hcomplete (E i) (hEpos i) (hEzero i)
    have hden := d4ThetaTeukolskyAngularQ_ofReal_add_two_ne_zero (hEpos i)
    unfold d4HBFiniteLocalAngularThresholdFullCoefficient
      d4HBFiniteLocalAngularThresholdCoefficient at hcancel
    rw [d4FundamentalQNMCrossBranchChiralMassJetNumerator_eq] at hcancel
    change (((X + C 2) * P - C 12).eval (q i)) = 0
    simp only [eval_sub, eval_mul, eval_add, eval_X, eval_C]
    dsimp [q] at hcancel ⊢
    field_simp [hden] at hcancel
    linear_combination hcancel
  have hRzero : R = 0 := by
    apply Bottcher.eq_zero_of_card_roots_gt_natDegree R S hRroots
    omega
  have heval := congrArg (fun T : ℂ[X] => T.eval (-2)) hRzero
  change (((X + C 2) * P - C 12).eval (-2)) = (0 : ℂ[X]).eval (-2) at heval
  norm_num at heval

/-- Closed route class: no single finite-order local angular threshold operator supplies universal
HB AIME cancellation on the unconditional positive Hardy-line Xi family. -/
def D4HBFiniteLocalAngularThresholdCancellationRouteKilled : Prop :=
  ∀ P : ℂ[X], ¬ D4HBFiniteLocalAngularThresholdXiComplete P

/-- Premise-free certificate killing the full finite-local-angular HB threshold route class. -/
theorem d4HBFiniteLocalAngularThresholdCancellationRouteKilled :
    D4HBFiniteLocalAngularThresholdCancellationRouteKilled := by
  exact not_d4HBFiniteLocalAngularThresholdXiComplete

end

end RHTower
