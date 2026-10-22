import GaloisForLFunctions.HTGeometry.FZZCigarTorusReplicaNeutrality
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint

/-!
# Critical FZZ neutral-screening / Parikh--Wilczek recoil endpoint

This endpoint discards static horizon-dilation completeness and generic
KMS/passivity.  Its input is irreducibly black-hole-specific:

* exact FZZ cigar scattering gives charge-`m` delay `exp (-m t)`;
* torus monodromy permits only neutral `W⁺W⁻` screening depth `k`, with
  coefficient `μ^(2k)/(k!)²`;
* finite-mass Parikh--Wilczek recoil inserts `m^k t^(2k)`, whose Mellin
  transform is `Gamma(s+2k) zeta(s+k)`.

Identifying the FZZ neutral depth with the Parikh--Wilczek recoil depth is the
new cross-regime physical bridge, not an established equivalence of the cigar
and four-dimensional Schwarzschild theories.  The coefficient theorem below
proves what follows exactly once that same-depth identification is made.

Consequently the fixed-charge neutral recoil series has the paper identity

`exp(-m t) * sum_k (μ² m t²)^k/(k!)²
  = exp(-m t) * I₀(2 μ t sqrt(m))`.

The modified-Bessel exponential envelope is

`exp((-m + 2 μ sqrt(m)) t) / sqrt(t)`.

Thus charge `m=n+1` becomes marginal at `μ=sqrt(m)/2`.  The square of this
FZZ condensate wall is exactly the Parikh--Wilczek finite-energy endpoint
action `m/4`.  The first charge alone is marginal at `μ=1/2`; every higher
charge still decays.  This gives a sharp nonperturbative phase boundary rather
than a perturbative or representation-theoretic relabeling.

At the first wall the critical charge has tail `t^(-1/2)`.  Its forward Mellin
chart has real tail power `Re(s)-3/2`; the CPT/reflection chart has power
`-Re(s)-1/2`.  They are simultaneously logarithmic exactly at `Re(s)=1/2`.

**[FALSIFIED PRODUCER]** The fractional-winding area tangent is not a
single-valued torus field by itself; only the full neutral `W⁺W⁻` insertion is.
That neutrality does not force one logarithmic subtraction shared by the
forward and reverse Mellin charts.  Complex powers of analytic functions have
meromorphic distributional extensions, so off-line powers can also be
renormalized; see Dang, arXiv:1503.00995, and Bergbauer--Brunetti--Kreimer,
arXiv:0908.0633.  The predicate below is therefore only an exact RH-strength
receiver/no-go: its algebra is valid, but torus locality or counterterm
existence cannot supply it.  Halder--Jafferis leave the actual torus one-point
function open, and its evaluation would need additional nonlocal dynamics.

The Lean-proved content is the coefficient weld, all-depth mixing, exact wall
hierarchy, sharp stability classification, critical tail-power calculation,
and endpoint equivalence.  It does not formalize the `I₀` asymptotic or claim
the open torus sewing law.

Physics sources: Parikh--Wilczek, arXiv:hep-th/9907001; Giveon--Itzhaki--Kutasov,
arXiv:1912.06538; Brustein--Zigdon, arXiv:2107.09001; Halder--Jafferis,
arXiv:2402.00932.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.FZZCigar

/-! ## Neutral winding-screening / recoil coefficients -/

/-- Coefficient at neutral FZZ screening depth `k` after inserting the exact
finite-mass Parikh--Wilczek Mellin jet. -/
def fzzParikhWilczekNeutralRecoilCoefficient
    (μ : ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  neutralScreeningCoefficient μ k *
    schwarzschildParikhWilczekMellinJet k s

/-- Exact coefficient weld.  FZZ torus neutrality supplies precisely the two
factorials required by the Parikh--Wilczek Borel tower. -/
theorem fzzParikhWilczekNeutralRecoilCoefficient_eq
    (μ : ℂ) (k : ℕ) (s : ℂ) :
    fzzParikhWilczekNeutralRecoilCoefficient μ k s =
      μ ^ (2 * k) *
        schwarzschildParikhWilczekFirstWindingBorelCoefficient s k *
          riemannZeta (s + (k : ℂ)) := by
  have hfac : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  rw [fzzParikhWilczekNeutralRecoilCoefficient,
    neutralScreeningCoefficient,
    schwarzschildParikhWilczekMellinJet,
    schwarzschildParikhWilczekFirstWindingBorelCoefficient]
  field_simp [hfac]

/-- A depth-zero zeta-dark scattering mode stays dark before recoil. -/
theorem fzzParikhWilczekNeutralRecoilCoefficient_zero_of_zeta_zero
    (μ : ℂ) {s : ℂ} (hs : riemannZeta s = 0) :
    fzzParikhWilczekNeutralRecoilCoefficient μ 0 s = 0 := by
  rw [fzzParikhWilczekNeutralRecoilCoefficient]
  exact mul_eq_zero_of_right _
    (schwarzschildParikhWilczekMellinJet_zero_of_zeta_zero hs)

/-- Every positive neutral FZZ screening depth activates every positive-real-
part scattering sector when the winding condensate is nonzero. -/
theorem fzzParikhWilczekNeutralRecoilCoefficient_ne_zero
    {μ : ℂ} (hμ : μ ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    {s : ℂ} (hs : 0 < s.re) :
    fzzParikhWilczekNeutralRecoilCoefficient μ k s ≠ 0 := by
  exact mul_ne_zero
    (neutralScreeningCoefficient_ne_zero hμ k)
    (schwarzschildParikhWilczekMellinJet_ne_zero hk hs)

/-- Source-faithful mixing law: every theta/Xi mode is dark at neutral depth
zero and bright at every positive FZZ screening/recoil depth. -/
theorem thetaXi_fzzParikhWilczekNeutralRecoil_all_positive_depths_ne_zero
    {μ : ℂ} (hμ : μ ≠ 0) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hxi : xi s = 0) :
    fzzParikhWilczekNeutralRecoilCoefficient μ 0 s = 0 ∧
      ∀ k : ℕ, 1 ≤ k →
        fzzParikhWilczekNeutralRecoilCoefficient μ k s ≠ 0 := by
  have hjet :=
    thetaXi_schwarzschildParikhWilczekMellinJet_all_positive_orders_ne_zero
      hs0 hs1 hxi
  constructor
  · rw [fzzParikhWilczekNeutralRecoilCoefficient, hjet.1, mul_zero]
  · intro k hk
    exact mul_ne_zero
      (neutralScreeningCoefficient_ne_zero hμ k) (hjet.2 k hk)

/-! ## Exact condensate-wall / finite-energy-action correspondence -/

/-- Critical neutral-condensate amplitude of charge `n+1`. -/
def fzzParikhWilczekNeutralChargeWall (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) + 1) / 2

/-- Large-`t` exponential rate of the charge-`n+1` Bessel-dressed FZZ delay. -/
def fzzParikhWilczekNeutralChargeExponent (μ : ℝ) (n : ℕ) : ℝ :=
  -((n : ℝ) + 1) +
    2 * μ * Real.sqrt ((n : ℝ) + 1)

/-- Squared neutral-condensate walls are exactly the nonperturbative
Parikh--Wilczek endpoint actions. -/
theorem fzzParikhWilczekNeutralChargeWall_sq (n : ℕ) :
    fzzParikhWilczekNeutralChargeWall n ^ 2 =
      schwarzschildParikhWilczekEndpointAction n := by
  rw [fzzParikhWilczekNeutralChargeWall,
    schwarzschildParikhWilczekEndpointAction]
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [div_pow, Real.sq_sqrt hn]
  norm_num

/-- First FZZ condensate wall is the critical amplitude `1/2`. -/
theorem fzzParikhWilczekNeutralChargeWall_zero :
    fzzParikhWilczekNeutralChargeWall 0 = 1 / 2 := by
  norm_num [fzzParikhWilczekNeutralChargeWall]

/-- Each charge is exactly marginal at its own condensate wall. -/
theorem fzzParikhWilczekNeutralChargeExponent_at_wall (n : ℕ) :
    fzzParikhWilczekNeutralChargeExponent
      (fzzParikhWilczekNeutralChargeWall n) n = 0 := by
  rw [fzzParikhWilczekNeutralChargeExponent,
    fzzParikhWilczekNeutralChargeWall]
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  nlinarith [Real.sq_sqrt hn]

private theorem sqrt_natCast_add_one_le_self (n : ℕ) :
    Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  exact (Real.sqrt_le_iff).2 ⟨by positivity, by nlinarith⟩

private theorem sqrt_natCast_add_one_pos (n : ℕ) :
    0 < Real.sqrt ((n : ℝ) + 1) := by
  exact Real.sqrt_pos.2 (by positivity)

/-- Below the first wall every charge decays strictly, and no larger interval
has this property. -/
theorem fzzParikhWilczek_all_charges_strictly_stable_iff (μ : ℝ) :
    (∀ n : ℕ, fzzParikhWilczekNeutralChargeExponent μ n < 0) ↔
      μ < 1 / 2 := by
  constructor
  · intro h
    have h0 := h 0
    norm_num [fzzParikhWilczekNeutralChargeExponent] at h0
    linarith
  · intro hμ n
    rw [fzzParikhWilczekNeutralChargeExponent]
    have hsqrtpos := sqrt_natCast_add_one_pos n
    have hsqrtle := sqrt_natCast_add_one_le_self n
    have hscale : 2 * μ < 1 := by linarith
    nlinarith

/-- Closed stability chamber for the full neutral charge tower. -/
theorem fzzParikhWilczek_all_charges_stable_iff (μ : ℝ) :
    (∀ n : ℕ, fzzParikhWilczekNeutralChargeExponent μ n ≤ 0) ↔
      μ ≤ 1 / 2 := by
  constructor
  · intro h
    have h0 := h 0
    norm_num [fzzParikhWilczekNeutralChargeExponent] at h0
    linarith
  · intro hμ n
    rw [fzzParikhWilczekNeutralChargeExponent]
    have hsqrtnonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) :=
      Real.sqrt_nonneg _
    have hsqrtle := sqrt_natCast_add_one_le_self n
    have hscale : 2 * μ ≤ 1 := by linarith
    nlinarith

/-- At critical amplitude only the first charge is marginal; every higher
FZZ scattering charge remains exponentially damped. -/
theorem fzzParikhWilczek_first_charge_uniquely_marginal :
    fzzParikhWilczekNeutralChargeExponent (1 / 2) 0 = 0 ∧
      ∀ n : ℕ, 1 ≤ n →
        fzzParikhWilczekNeutralChargeExponent (1 / 2) n < 0 := by
  constructor
  · norm_num [fzzParikhWilczekNeutralChargeExponent]
  · intro n hn
    rw [fzzParikhWilczekNeutralChargeExponent]
    have hbase : (1 : ℝ) < (n : ℝ) + 1 := by
      exact_mod_cast Nat.lt_add_one_iff.mpr hn
    have hnonneg : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hsqrtlt : Real.sqrt ((n : ℝ) + 1) < (n : ℝ) + 1 := by
      rw [Real.sqrt_lt hnonneg (by positivity)]
      nlinarith
    nlinarith

/-- Above critical amplitude the first winding charge already grows. -/
theorem fzzParikhWilczek_first_charge_unstable_iff (μ : ℝ) :
    0 < fzzParikhWilczekNeutralChargeExponent μ 0 ↔
      1 / 2 < μ := by
  norm_num [fzzParikhWilczekNeutralChargeExponent]
  constructor <;> intro h <;> linarith

/-- Higher-charge condensation walls are strictly farther away. -/
theorem fzzParikhWilczekNeutralChargeWall_strictMono :
    StrictMono fzzParikhWilczekNeutralChargeWall := by
  intro m n hmn
  rw [fzzParikhWilczekNeutralChargeWall,
    fzzParikhWilczekNeutralChargeWall]
  apply div_lt_div_of_pos_right _ (by norm_num)
  apply Real.sqrt_lt_sqrt (by positivity)
  exact_mod_cast Nat.add_lt_add_right hmn 1

/-! ## Falsified critical torus-sewing receiver -/

/-- Tail power after multiplying the critical `t^(-1/2)` charge by the
forward Mellin density `t^(s-1)`. -/
def fzzParikhWilczekCriticalForwardMellinTailPower (s : ℂ) : ℝ :=
  s.re - 3 / 2

/-- Tail power after multiplying the same critical charge by the reflected
Mellin density `t^(-s)`. -/
def fzzParikhWilczekCriticalReverseMellinTailPower (s : ℂ) : ℝ :=
  -s.re - 1 / 2

/-- Pointwise equal-log-tail condition.  This is an algebraic receiver, not a
consequence of local renormalizability: unequal complex powers also admit
meromorphic distributional extensions. -/
def FZZParikhWilczekCriticalNeutralTorusLogSewable (s : ℂ) : Prop :=
  fzzParikhWilczekCriticalForwardMellinTailPower s = -1 ∧
    fzzParikhWilczekCriticalReverseMellinTailPower s = -1

/-- Critical neutral torus log-sewing is exactly critical-line placement. -/
theorem fzzParikhWilczekCriticalNeutralTorusLogSewable_iff (s : ℂ) :
    FZZParikhWilczekCriticalNeutralTorusLogSewable s ↔
      s.re = 1 / 2 := by
  rw [FZZParikhWilczekCriticalNeutralTorusLogSewable,
    fzzParikhWilczekCriticalForwardMellinTailPower,
    fzzParikhWilczekCriticalReverseMellinTailPower]
  constructor
  · rintro ⟨h, _⟩
    linarith
  · intro h
    constructor <;> linarith

/-- **[FALSIFIED AS A COUNTERTERM PRODUCER]** Formal receiver asserting that
every theta/Xi dark sector has matching logarithmic tail degrees. -/
def ThetaFZZParikhWilczekCriticalNeutralTorusSewing : Prop :=
  ∀ s : ℂ, xi s = 0 →
    FZZParikhWilczekCriticalNeutralTorusLogSewable s

/-- **Critical neutral-screening/recoil receiver.**  Matching both formal tail
degrees has exactly RH strength; neutral torus renormalization does not prove
this predicate. -/
theorem riemannHypothesis_iff_thetaFZZParikhWilczekCriticalNeutralTorusSewing :
    RiemannHypothesis ↔
      ThetaFZZParikhWilczekCriticalNeutralTorusSewing := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  constructor
  · intro h s hs
    exact (fzzParikhWilczekCriticalNeutralTorusLogSewable_iff s).2 (h s hs)
  · intro h s hs
    exact (fzzParikhWilczekCriticalNeutralTorusLogSewable_iff s).1 (h s hs)

end

end RHTower
