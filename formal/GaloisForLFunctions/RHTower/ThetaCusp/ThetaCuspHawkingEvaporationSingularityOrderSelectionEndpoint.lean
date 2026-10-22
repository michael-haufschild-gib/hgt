import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFullMirrorWeakCouplingOrderEndpoint

/-!
# Conditional surface-gravity-power selector for theta-mirror coupling order

This endpoint tests a Hawking-specific selector which is absent from stationary KMS, CCR,
unitarity, inverse, Krein, and generic mixing laws: finite accumulated load through the terminal
Schwarzschild evaporation singularity.

In the semiclassical mass-loss model

`dM/du = -alpha/M^(2 : ℕ)`,  `kappa(M) = 1/(4M)`,

the remaining evaporation time is `M^(3 : ℕ)/(3 alpha)`.  On dyadic mass shells
`M_n = 2^(-n)`, the time spent between `M_n` and `M_n/2` is exactly
`7 M_n^(3 : ℕ)/(24 alpha)`.  If a scattering sector first appears at coupling order `m` and its
endpoint intensity follows the surface-gravity law `kappa^(2m)`, its shell load is a fixed
positive constant times

`M_n^(3-2m) = (2^(2m)/8)^n`.

This gives a sharp singularity classification.  The standard first-order channel (`m = 1`) has
summable endpoint load.  Every delayed channel (`m >= 2`) has shell load at least one and is not
summable.  Since the exact nonlinear theta mirror has a finite positive first coupling order in
every sector, universal finite terminal load forces every noncentral sector to have order one.
The existing source-faithful full-mirror theorem then gives RH.

**[PAPER-PROVED] [LEAN-PROVED] [HAWKING-SPECIFIC]** The Schwarzschild shell-time identity,
load normal form, summability classification, order-one selection, and final conditional RH
equivalence are exact.

**[FALSIFIED PHYSICAL WELD]** The displayed summability classification is exact for the reporter
`kappa^(2*m)`, but that reporter is not selected by the actual mass-dilated Davies--Fulling theta
mirror.  `ThetaCuspHawkingMassDilationOrderBlindnessNoGo` proves that coupling order is invariant
under `p_M(u) = M p(u/M)`, while the Schwarzian flux always has the single mass weight `M^(-2)`.
Exact shell load is therefore proportional to `M`, summable for every onset order.  The
conditional implications below remain algebraically valid; they are not a Hawking producer.

**[FALSIFICATION BOUNDARY]** A remnant, Planck cutoff, or any finite truncation of the dyadic
shells makes every coupling order summable; this is proved below.  Strong-coupling saturation can
likewise destroy the selector.  Thus the endpoint is genuinely about complete evaporation and its
terminal singularity, not another reformulation of KMS passivity or finite-coupling mixing.

Semiclassical mass-loss provenance: Massar, arXiv:gr-qc/9411039; Brout--Massar--Parentani--Spindel,
arXiv:0710.4345.  Endpoint-breakdown warning: Lowe--Thorlacius, arXiv:2605.00780.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## Exact Schwarzschild evaporation clock -/

/-- Schwarzschild surface gravity in units `G = c = hbar = 1`. -/
def schwarzschildSurfaceGravity (M : ℝ) : ℝ :=
  1 / (4 * M)

/-- Remaining lifetime obtained by integrating `dM/du = -alpha/M^(2 : ℕ)` down to zero mass. -/
def schwarzschildEvaporationRemainingTime (alpha M : ℝ) : ℝ :=
  M ^ 3 / (3 * alpha)

/-- Normalized dyadic evaporation mass shell `M_n = 2^(-n)`. -/
def schwarzschildEvaporationDyadicMass (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n

/-- Retarded time spent while the normalized mass falls from `M_n` to `M_(n+1)`. -/
def schwarzschildEvaporationDyadicShellDuration (alpha : ℝ) (n : ℕ) : ℝ :=
  schwarzschildEvaporationRemainingTime alpha
      (schwarzschildEvaporationDyadicMass n) -
    schwarzschildEvaporationRemainingTime alpha
      (schwarzschildEvaporationDyadicMass (n + 1))

theorem schwarzschildEvaporationDyadicMass_succ (n : ℕ) :
    schwarzschildEvaporationDyadicMass (n + 1) =
      schwarzschildEvaporationDyadicMass n / 2 := by
  rw [schwarzschildEvaporationDyadicMass, schwarzschildEvaporationDyadicMass,
    pow_succ]
  ring

/-- Exact Hawking lifetime of one dyadic mass shell. -/
theorem schwarzschildEvaporationDyadicShellDuration_eq
    {alpha : ℝ} (halpha : alpha ≠ 0) (n : ℕ) :
    schwarzschildEvaporationDyadicShellDuration alpha n =
      7 / (24 * alpha) * schwarzschildEvaporationDyadicMass n ^ 3 := by
  rw [schwarzschildEvaporationDyadicShellDuration,
    schwarzschildEvaporationRemainingTime,
    schwarzschildEvaporationRemainingTime,
    schwarzschildEvaporationDyadicMass_succ]
  field_simp
  ring

/-! ## Surface-gravity load of an order-`m` scattering sector -/

/-- Literal shell duration times the order-`m` squared surface-gravity intensity. -/
def schwarzschildEvaporationDyadicSectorLoad
    (alpha : ℝ) (m n : ℕ) : ℝ :=
  schwarzschildEvaporationDyadicShellDuration alpha n *
    schwarzschildSurfaceGravity (schwarzschildEvaporationDyadicMass n) ^ (2 * m)

/-- Dimensionless shell dependence after removing the fixed positive factor depending on
`alpha` and `m`. -/
def schwarzschildEvaporationDyadicEndpointShellLoad (m n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (2 * m) / 8) ^ n

/-- A terminal cutoff retains only finitely many mass shells. -/
def schwarzschildEvaporationTruncatedEndpointShellLoad
    (cutoff m n : ℕ) : ℝ :=
  if n < cutoff then schwarzschildEvaporationDyadicEndpointShellLoad m n else 0

/-- Exact separation of physical constants from the singular dyadic shell exponent. -/
theorem schwarzschildEvaporationDyadicSectorLoad_eq
    {alpha : ℝ} (halpha : alpha ≠ 0) (m n : ℕ) :
    schwarzschildEvaporationDyadicSectorLoad alpha m n =
      (7 / (24 * alpha * 4 ^ (2 * m))) *
        schwarzschildEvaporationDyadicEndpointShellLoad m n := by
  rw [schwarzschildEvaporationDyadicSectorLoad,
    schwarzschildEvaporationDyadicShellDuration_eq halpha,
    schwarzschildSurfaceGravity,
    schwarzschildEvaporationDyadicMass,
    schwarzschildEvaporationDyadicEndpointShellLoad]
  field_simp
  have hmass : (1 / 2 : ℝ) ^ n ≠ 0 := by positivity
  have hcancel : (1 / ((1 / 2 : ℝ) ^ n * 4)) * 4 =
      1 / (1 / 2 : ℝ) ^ n := by
    field_simp
  rw [mul_assoc, ← mul_pow, hcancel, one_div_pow]
  norm_num
  rw [mul_comm, ← div_eq_mul_inv]
  rw [div_eq_iff (by positivity : ((2 : ℝ) ^ n) ^ 3 ≠ 0)]
  have hleft : ((2 : ℝ) ^ n) ^ (2 * m) = ((2 : ℝ) ^ (2 * m)) ^ n := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    exact Nat.mul_comm n (2 * m)
  have hright : ((2 : ℝ) ^ n) ^ 3 = (8 : ℝ) ^ n := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hleft, hright, ← mul_pow]
  congr 1
  field_simp

/-! ## Sharp endpoint summability classification -/

theorem schwarzschildEvaporationDyadicEndpointShellLoad_one (n : ℕ) :
    schwarzschildEvaporationDyadicEndpointShellLoad 1 n = (1 / 2 : ℝ) ^ n := by
  rw [schwarzschildEvaporationDyadicEndpointShellLoad]
  norm_num

/-- The standard first-order Hawking channel has finite accumulated endpoint load. -/
theorem summable_schwarzschildEvaporationDyadicEndpointShellLoad_one :
    Summable (schwarzschildEvaporationDyadicEndpointShellLoad 1) := by
  rw [show schwarzschildEvaporationDyadicEndpointShellLoad 1 =
      fun n => (1 / 2 : ℝ) ^ n by
    funext n
    exact schwarzschildEvaporationDyadicEndpointShellLoad_one n]
  simpa only [norm_div, norm_one, Real.norm_ofNat] using
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))

/-- Every delayed order has a non-decaying load on every terminal dyadic shell. -/
theorem one_le_schwarzschildEvaporationDyadicEndpointShellLoad
    {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    1 ≤ schwarzschildEvaporationDyadicEndpointShellLoad m n := by
  rw [schwarzschildEvaporationDyadicEndpointShellLoad]
  apply one_le_pow₀
  rw [one_le_div₀ (by norm_num : (0 : ℝ) < 8)]
  have hpow : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ (2 * m) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  norm_num at hpow ⊢
  linarith

/-- Every delayed scattering channel has infinite complete-evaporation endpoint load. -/
theorem not_summable_schwarzschildEvaporationDyadicEndpointShellLoad
    {m : ℕ} (hm : 2 ≤ m) :
    ¬ Summable (schwarzschildEvaporationDyadicEndpointShellLoad m) := by
  intro hsum
  have hzero := hsum.tendsto_atTop_zero
  have hevent : ∀ᶠ n : ℕ in atTop,
      schwarzschildEvaporationDyadicEndpointShellLoad m n < 1 :=
    (tendsto_order.1 hzero).2 1 zero_lt_one
  obtain ⟨n, hn⟩ := hevent.exists
  exact (not_lt_of_ge
    (one_le_schwarzschildEvaporationDyadicEndpointShellLoad hm n)) hn

/-- Sharp selection: a positive coupling order with finite complete endpoint load is one. -/
theorem schwarzschildEvaporationDyadicEndpointLoad_finite_forces_order_one
    {m : ℕ} (hm : 1 ≤ m)
    (hfinite : Summable (schwarzschildEvaporationDyadicEndpointShellLoad m)) :
    m = 1 := by
  by_contra hne
  have hm2 : 2 ≤ m := by omega
  exact not_summable_schwarzschildEvaporationDyadicEndpointShellLoad hm2 hfinite

/-- Falsification boundary: after any finite terminal cutoff, every order has finite load. -/
theorem summable_schwarzschildEvaporationTruncatedEndpointShellLoad
    (cutoff m : ℕ) :
    Summable (schwarzschildEvaporationTruncatedEndpointShellLoad cutoff m) := by
  apply summable_of_ne_finset_zero (s := Finset.range cutoff)
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  simp [schwarzschildEvaporationTruncatedEndpointShellLoad, hn]

/-! ## Theta-mirror singularity endpoint -/

/-- Proposed physical producer: every noncentral exact theta-mirror sector has finite accumulated
surface-gravity load through complete Schwarzschild evaporation. -/
def ThetaCuspHawkingSchwarzschildEndpointFiniteLoad : Prop :=
  ∀ (a w : ℝ) (ha : |a| < 1), a ≠ 0 →
    Summable (schwarzschildEvaporationDyadicEndpointShellLoad
      (thetaCuspHawkingFullMirrorSectorCouplingOrder a w ha))

theorem thetaCuspHawkingFullMirrorNoOrderJump_of_schwarzschildEndpointFiniteLoad
    (hload : ThetaCuspHawkingSchwarzschildEndpointFiniteLoad) :
    ThetaCuspHawkingFullMirrorNoOrderJump := by
  intro a w ha hane
  exact schwarzschildEvaporationDyadicEndpointLoad_finite_forces_order_one
    (thetaCuspHawkingFullMirrorSectorCouplingOrder_spec a w ha).1
    (hload a w ha hane)

/-- Finite terminal load is exactly the existing no-order-jump condition once the proposed
surface-gravity shell law is adopted. -/
theorem thetaCuspHawkingSchwarzschildEndpointFiniteLoad_iff_noOrderJump :
    ThetaCuspHawkingSchwarzschildEndpointFiniteLoad ↔
      ThetaCuspHawkingFullMirrorNoOrderJump := by
  constructor
  · exact thetaCuspHawkingFullMirrorNoOrderJump_of_schwarzschildEndpointFiniteLoad
  · intro horder a w ha hane
    rw [horder a w ha hane]
    exact summable_schwarzschildEvaporationDyadicEndpointShellLoad_one

/-- Conditional producer direction: finite load through the actual evaporation singularity
excludes every delayed tilted sector and proves RH. -/
theorem riemannHypothesis_of_thetaCuspHawkingSchwarzschildEndpointFiniteLoad
    (hload : ThetaCuspHawkingSchwarzschildEndpointFiniteLoad) :
    RiemannHypothesis :=
  riemannHypothesis_iff_thetaCuspHawkingFullMirrorNoOrderJump.2
    (thetaCuspHawkingFullMirrorNoOrderJump_of_schwarzschildEndpointFiniteLoad hload)

/-- Exact endpoint formulation: RH is universal finite complete-evaporation surface-gravity load,
conditional only in the physical interpretation of that load law. -/
theorem riemannHypothesis_iff_thetaCuspHawkingSchwarzschildEndpointFiniteLoad :
    RiemannHypothesis ↔ ThetaCuspHawkingSchwarzschildEndpointFiniteLoad :=
  riemannHypothesis_iff_thetaCuspHawkingFullMirrorNoOrderJump.trans
    thetaCuspHawkingSchwarzschildEndpointFiniteLoad_iff_noOrderJump.symm

/-- In particular, the proposed finite-load law excludes every off-critical Xi sector, hence also
the off-critical negative cubic chamber produced by selective Hawking stimulation. -/
theorem thetaCuspHawkingSchwarzschildEndpointFiniteLoad_excludes_offCritical
    (hload : ThetaCuspHawkingSchwarzschildEndpointFiniteLoad)
    (q : XiZeroCopy) :
    (q.1 : ℂ).re = 1 / 2 := by
  have hRH :=
    riemannHypothesis_of_thetaCuspHawkingSchwarzschildEndpointFiniteLoad hload
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  have him := congrArg Complex.im ht
  simp [xiSpectralPoint] at him
  linarith

end

end RHTower
