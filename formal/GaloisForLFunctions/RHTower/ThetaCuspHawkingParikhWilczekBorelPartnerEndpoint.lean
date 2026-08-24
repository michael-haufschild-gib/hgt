import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBackreactionJetEndpoint
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Parikh--Wilczek Borel-partner growth endpoint

Finite-mass Schwarzschild tunnelling produces more than generic KMS mixing.  Expanding the
Parikh--Wilczek winding

`exp (-n*x + epsilon*n*x^2)`

in the horizon-shrinkage parameter and taking its Mellin transform gives the order-`k` jet

`Gamma (s + 2*k) / n^(s+k)`.

After the second factorial normalization of a Borel transform, the first physical winding
`n = 1` therefore has coefficient

`b_k(s) = Gamma (s + 2*k) / (k!)^2`.

This file proves its exact consecutive growth law

`b_(k+1)(s) = R_k(s) b_k(s)`,

where

`R_k(s) = (s + 2*k) (s + 2*k + 1) / (k+1)^2`.

The functional-equation partner has a coefficient-faithful asymmetry at every Borel grade:

`R_k(s) - R_k(1-s) = 4 (2*k+1) (s-1/2) / (k+1)^2`.

Thus equality of the real partner growth rates is exactly critical-line placement, already at
one grade.  Requiring this balance at every actual Xi zero is equivalent to RH.

This is a new Hawking-specific reporter, not an RH proof.  Euler's exact hypergeometric partner
gauge has real squeeze `(1/2-Re(s))*log(1-z)`.  Its canonical doubled `SU(1,1)` completion therefore
has zero pair mixing exactly on the critical line and nonzero pair mixing in every tilted sector.
Generic KMS, CCR, unitarity, Cayley completion, and late Gaussian recoil neither contain the
coefficient-growth law nor force this squeeze to vanish.  A theta-dark-mode no-pair-creation law
would prove RH, but current positive recoil jets instead activate every zero sector; no such
physical producer is asserted here.

The tunnelling exponent is from Parikh--Wilczek, arXiv:hep-th/9907001.  Borel methods for black-hole
quasinormal expansions are established independently by Hatsuda, arXiv:1906.07232.  The physical
energy cutoff is the coalescing endpoint `x = 1/(2*epsilon)`.  Its `(n+1)`-st winding action is
`(n+1)/4`, so the first Borel wall at `1/4` is a finite-energy Hawking endpoint action rather than
an arbitrary resummation scale.  The associated Gauss-hypergeometric continuation has local
exponent `1/2-s`; that analytic continuation is paper-proved in the endpoint ledger but is not
asserted in this file.

Claim labels: `[PAPER-PROVED] [LEAN-PROVED] [HAWKING-SPECIFIC] [LOCAL-RESEARCH]`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Dimensionless upper energy endpoint `E = M` after setting
`x = 8*pi*M*E` and `epsilon = 1/(16*pi*M^2)`. -/
def schwarzschildParikhWilczekDimensionlessEnergyEndpoint (epsilon : ℝ) : ℝ :=
  1 / (2 * epsilon)

/-- Exponent of the `(n+1)`-st exact Parikh--Wilczek Bose winding before applying `exp`. -/
def schwarzschildParikhWilczekWindingPhase
    (n : ℕ) (epsilon x : ℝ) : ℝ :=
  -((n : ℝ) + 1) * x + epsilon * (((n : ℝ) + 1) * x ^ 2)

/-- Nonperturbative action of the `(n+1)`-st winding at the physical energy endpoint. -/
def schwarzschildParikhWilczekEndpointAction (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) / 4

/-- At the physical cutoff the tunnelling phase is exactly `-A_n/epsilon`. -/
theorem schwarzschildParikhWilczekWindingPhase_energyEndpoint
    (n : ℕ) {epsilon : ℝ} (hepsilon : epsilon ≠ 0) :
    schwarzschildParikhWilczekWindingPhase n epsilon
        (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon) =
      -schwarzschildParikhWilczekEndpointAction n / epsilon := by
  rw [schwarzschildParikhWilczekWindingPhase,
    schwarzschildParikhWilczekDimensionlessEnergyEndpoint,
    schwarzschildParikhWilczekEndpointAction]
  field_simp [hepsilon]
  ring

/-- Exact source weld: endpoint actions are the exponentially small sectors of the physical
finite-energy Hawking winding, with no generic KMS assumption. -/
theorem schwarzschildParikhWilczekWindingTerm_energyEndpoint
    (n : ℕ) {epsilon : ℝ} (hepsilon : epsilon ≠ 0) :
    schwarzschildParikhWilczekWindingTerm n epsilon
        (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon) =
      Real.exp (-schwarzschildParikhWilczekEndpointAction n / epsilon) := by
  rw [schwarzschildParikhWilczekWindingTerm]
  congr 1
  exact schwarzschildParikhWilczekWindingPhase_energyEndpoint n hepsilon

/-- First Bose winding produces the nearest Hawking endpoint action `1/4`. -/
theorem schwarzschildParikhWilczekEndpointAction_zero :
    schwarzschildParikhWilczekEndpointAction 0 = 1 / 4 := by
  norm_num [schwarzschildParikhWilczekEndpointAction]

/-- Higher Bose windings give strictly more distant endpoint actions `1/2, 3/4, ...`; hence they
cannot share the first winding's nearest Borel wall. -/
theorem schwarzschildParikhWilczekEndpointAction_strictMono :
    StrictMono schwarzschildParikhWilczekEndpointAction := by
  intro m n hmn
  rw [schwarzschildParikhWilczekEndpointAction,
    schwarzschildParikhWilczekEndpointAction]
  exact div_lt_div_of_pos_right
    (by exact_mod_cast Nat.add_lt_add_right hmn 1) (by norm_num)

/-- Real squeeze parameter of the exact Euler partner gauge
`(1-z)^(1/2-s)` at the first Parikh--Wilczek Borel wall.  Here `z=4*xi` and the physical
approach to the first wall is `0<z<1`. -/
def schwarzschildParikhWilczekBorelMirrorLogSqueeze
    (s : ℂ) (z : ℝ) : ℝ :=
  (1 / 2 - s.re) * Real.log (1 - z)

/-- Off-diagonal coefficient of the canonical two-mode Hawking/Bogoliubov completion of the
Euler partner gauge. -/
def schwarzschildParikhWilczekBorelMirrorPairMixing
    (s : ℂ) (z : ℝ) : ℝ :=
  Real.sinh (schwarzschildParikhWilczekBorelMirrorLogSqueeze s z)

/-- Inside the physical first-wall interval, vanishing pair mixing is exactly critical-line
placement.  Thus every tilted Borel partner requires a nontrivial Hawking two-mode squeeze. -/
theorem schwarzschildParikhWilczekBorelMirrorPairMixing_eq_zero_iff
    (s : ℂ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    schwarzschildParikhWilczekBorelMirrorPairMixing s z = 0 ↔
      s.re = 1 / 2 := by
  have hlogneg : Real.log (1 - z) < 0 :=
    Real.log_neg (by linarith) (by linarith)
  have hlog : Real.log (1 - z) ≠ 0 := ne_of_lt hlogneg
  rw [schwarzschildParikhWilczekBorelMirrorPairMixing,
    Real.sinh_eq_zero, schwarzschildParikhWilczekBorelMirrorLogSqueeze,
    mul_eq_zero]
  simp only [hlog, or_false]
  constructor <;> intro h <;> linarith

/-- Equivalent tilted-sector form: every off-critical sector mixes at every finite approach to
the first physical recoil wall. -/
theorem schwarzschildParikhWilczekBorelMirrorPairMixing_ne_zero_iff
    (s : ℂ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    schwarzschildParikhWilczekBorelMirrorPairMixing s z ≠ 0 ↔
      s.re ≠ 1 / 2 := by
  exact not_congr
    (schwarzschildParikhWilczekBorelMirrorPairMixing_eq_zero_iff s hz0 hz1)

/-- Canonical nonperturbative `SU(1,1)` norm law for the Borel mirror completion. -/
theorem schwarzschildParikhWilczekBorelMirror_bogoliubov_norm
    (s : ℂ) (z : ℝ) :
    Real.cosh (schwarzschildParikhWilczekBorelMirrorLogSqueeze s z) ^ 2 -
        schwarzschildParikhWilczekBorelMirrorPairMixing s z ^ 2 = 1 := by
  rw [schwarzschildParikhWilczekBorelMirrorPairMixing]
  exact Real.cosh_sq_sub_sinh_sq _

/-- Borel-normalized coefficient of the first Parikh--Wilczek Bose winding at backreaction
grade `k`.  One factorial comes from the `epsilon` Taylor expansion and the second from the Borel
transform. -/
def schwarzschildParikhWilczekFirstWindingBorelCoefficient
    (s : ℂ) (k : ℕ) : ℂ :=
  Complex.Gamma (s + 2 * (k : ℂ)) / ((k.factorial : ℂ) ^ 2)

/-- Exact weld to the existing finite-mass Mellin jet: restoring both factorials and summing the
Bose windings contributes precisely the shifted zeta factor. -/
theorem schwarzschildParikhWilczekMellinJet_eq_factorialSq_mul_firstWindingBorelCoefficient
    (k : ℕ) (s : ℂ) :
    schwarzschildParikhWilczekMellinJet k s =
      (k.factorial : ℂ) ^ 2 *
        schwarzschildParikhWilczekFirstWindingBorelCoefficient s k *
          riemannZeta (s + (k : ℂ)) := by
  have hfac : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  rw [schwarzschildParikhWilczekMellinJet,
    schwarzschildParikhWilczekFirstWindingBorelCoefficient]
  field_simp [hfac]

/-- Consecutive Borel-coefficient growth ratio forced by the quadratic horizon-shrinkage term. -/
def schwarzschildParikhWilczekFirstWindingBorelGrowthRatio
    (s : ℂ) (k : ℕ) : ℂ :=
  ((s + 2 * (k : ℂ)) * (s + 2 * (k : ℂ) + 1)) /
    (((k + 1 : ℕ) : ℂ) ^ 2)

/-- Exact first-winding Borel recurrence.  Positive real part keeps both Gamma recurrence steps
away from their totalized poles. -/
theorem schwarzschildParikhWilczekFirstWindingBorelCoefficient_succ
    (s : ℂ) (k : ℕ) (hs : 0 < s.re) :
    schwarzschildParikhWilczekFirstWindingBorelCoefficient s (k + 1) =
      schwarzschildParikhWilczekFirstWindingBorelGrowthRatio s k *
        schwarzschildParikhWilczekFirstWindingBorelCoefficient s k := by
  have hz : s + 2 * (k : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hz1 : s + 2 * (k : ℂ) + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hkfac : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hsucc : (((k + 1).factorial : ℕ) : ℂ) =
      (k + 1 : ℂ) * (k.factorial : ℂ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring_nf
  rw [schwarzschildParikhWilczekFirstWindingBorelCoefficient,
    schwarzschildParikhWilczekFirstWindingBorelGrowthRatio,
    schwarzschildParikhWilczekFirstWindingBorelCoefficient, hsucc]
  rw [show s + 2 * (((k + 1 : ℕ) : ℂ)) =
      (s + 2 * (k : ℂ) + 1) + 1 by push_cast; ring,
    Complex.Gamma_add_one _ hz1,
    Complex.Gamma_add_one _ hz]
  have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  field_simp [hkfac, hk1]
  push_cast
  ring_nf

/-- Exact functional-equation partner asymmetry at every Borel grade. -/
theorem schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_sub_partner
    (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekFirstWindingBorelGrowthRatio s k -
        schwarzschildParikhWilczekFirstWindingBorelGrowthRatio (1 - s) k =
      4 * (2 * (k : ℂ) + 1) * (s - 1 / 2) /
        (((k + 1 : ℕ) : ℂ) ^ 2) := by
  rw [schwarzschildParikhWilczekFirstWindingBorelGrowthRatio,
    schwarzschildParikhWilczekFirstWindingBorelGrowthRatio]
  have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  field_simp [hk1]
  ring

/-- Real partner-growth imbalance is a positive grade factor times transverse displacement from
the critical line. -/
theorem schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_re_sub_partner
    (s : ℂ) (k : ℕ) :
    (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio s k).re -
        (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio (1 - s) k).re =
      (4 * (2 * (k : ℝ) + 1) * (s.re - 1 / 2)) /
        (k + 1 : ℝ) ^ 2 := by
  rw [← Complex.sub_re,
    schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_sub_partner]
  push_cast
  norm_num [Complex.div_re, Complex.normSq_apply, pow_two,
    Complex.mul_re, Complex.mul_im]
  field_simp

/-- At any one Borel grade, equal real growth of the Hawking/CPT partner pair is exactly
critical-line placement. -/
theorem schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_partner_re_eq_iff
    (s : ℂ) (k : ℕ) :
    (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio s k).re =
        (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio (1 - s) k).re ↔
      s.re = 1 / 2 := by
  rw [← sub_eq_zero,
    schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_re_sub_partner]
  have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  constructor
  · intro hzero
    have hden : (k + 1 : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp [hden] at hzero
    have hfactor : 0 < 4 * (2 * (k : ℝ) + 1) := by positivity
    nlinarith
  · intro hs
    rw [hs]
    norm_num

/-- Every completed Xi mode has balanced real growth against its functional-equation partner in
the first-winding Parikh--Wilczek Borel tower. -/
def SchwarzschildParikhWilczekBorelPartnerBalanced : Prop :=
  ∀ s : ℂ, xi s = 0 → ∀ k : ℕ,
    (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio s k).re =
      (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio (1 - s) k).re

/-- **Parikh--Wilczek Borel-partner endpoint.**  Universal first-winding growth balance is
equivalent to RH.  The physical work left is to derive balance from finite-mass evaporation, not
to assume this endpoint predicate. -/
theorem riemannHypothesis_iff_schwarzschildParikhWilczekBorelPartnerBalanced :
    RiemannHypothesis ↔ SchwarzschildParikhWilczekBorelPartnerBalanced := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h s hs k
    exact
      (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_partner_re_eq_iff
        s k).2 (h s hs)
  · intro h s hs
    exact
      (schwarzschildParikhWilczekFirstWindingBorelGrowthRatio_partner_re_eq_iff
        s 0).1 (h s hs 0)

end

end RHTower
