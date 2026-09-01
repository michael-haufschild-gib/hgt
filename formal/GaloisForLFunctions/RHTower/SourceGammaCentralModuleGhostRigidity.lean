import GaloisForLFunctions.RHTower.SourceGammaChannelPositiveHermitianScalarizationNoGo

/-!
# Central module-valued source--Gamma ghosts are rigid

The scalar shared-ghost obstruction, channel-resolved projection no-go, and positive Hermitian
scalarization no-go leave one apparent escape: replace the scalar ghost by a matrix or operator
while keeping the physical prime--Gamma rotations as central characters.

This file classifies that escape without a dimension, topology, positivity, invertibility, or
boundedness assumption.  Let `u` and `v` be prime-independent forward and reflected ghost legs in
any real module.  At one prime `p`, the central Ward equation fits the reflected leg exactly as

`v = p^(2*t) • u`.

If the same nonzero forward leg satisfies the equation at primes two and three, torsion-freeness
gives `2^(2*t) = 3^(2*t)`, hence `t = 0`.  Thus enlarging the ghost to a matrix, finite-rank
operator, or arbitrary real module does not evade the shared wall while the Gamma action remains
central and prime-independent.

For every positive matrix size, existence of such a nonzero central ghost at every actual Xi
divisor is therefore equivalent to RH and to the common HB/FZZ-P/PW-B/RBH Ward endpoint.  This is
a route-class kill, not a construction of source naturality.  The sharp survivor is genuinely
prime-mixing, noncentral source dynamics before projection or scalarization.

`[NEW] [SHARED-WARD ROUTE-CLASS NO-GO] [SOURCE-PURE] [LEAN-PROVED]`
-/

open Complex Matrix

namespace RHTower

noncomputable section

/-- Central physical Gamma Ward equation for prime-independent forward and reflected ghost legs
in an arbitrary real module.  The scalar equation is the special case `u = c`, `v = c⁻¹`. -/
def primeGammaCentralModuleGhostWardEquation
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (u v : V) (t : ℝ) (p : Nat.Primes) : Prop :=
  primeGammaPhysicalRotationDeterminant t p • u =
    primeGammaPhysicalRotationDeterminant (-t) p • v

/-- One prime fits the reflected module-valued ghost leg uniquely along the ray of the forward
leg.  No inverse, positivity, finite-dimensionality, or topology is used. -/
theorem primeGammaCentralModuleGhostWardEquation_fitted
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {u v : V} {t : ℝ} {p : Nat.Primes}
    (h : primeGammaCentralModuleGhostWardEquation u v t p) :
    ((p : ℝ) ^ (2 * t)) • u = v := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have h' : ((p : ℝ) ^ t) • u = ((p : ℝ) ^ (-t)) • v := by
    simpa [primeGammaCentralModuleGhostWardEquation,
      primeGammaPhysicalRotationDeterminant] using h
  have hs := congrArg (fun w : V => ((p : ℝ) ^ t) • w) h'
  rw [smul_smul, smul_smul] at hs
  have hleft : (p : ℝ) ^ t * (p : ℝ) ^ t = (p : ℝ) ^ (2 * t) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have hright : (p : ℝ) ^ t * (p : ℝ) ^ (-t) = 1 := by
    rw [← Real.rpow_add hp]
    simp
  rw [hleft, hright, one_smul] at hs
  exact hs

/-- **Rank-free central-character rigidity.**  A nonzero prime-independent module-valued ghost
cannot satisfy the central physical Gamma Ward equation at primes two and three away from neutral
horizontal grade. -/
theorem primeGammaCentralModuleGhost_two_three_rigidity
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {u v : V} (hu : u ≠ 0) (t : ℝ)
    (htwo : primeGammaCentralModuleGhostWardEquation
      u v t deningerCalderonWittPrimeTwo)
    (hthree : primeGammaCentralModuleGhostWardEquation
      u v t deningerCalderonWittPrimeThree) :
    t = 0 := by
  have htwo' := primeGammaCentralModuleGhostWardEquation_fitted htwo
  have hthree' := primeGammaCentralModuleGhostWardEquation_fitted hthree
  have hsmul : ((2 : ℝ) ^ (2 * t)) • u = ((3 : ℝ) ^ (2 * t)) • u := by
    simpa [deningerCalderonWittPrimeTwo, deningerCalderonWittPrimeThree] using
      htwo'.trans hthree'.symm
  have hpowers : (2 : ℝ) ^ (2 * t) = (3 : ℝ) ^ (2 * t) := by
    have hz : (((2 : ℝ) ^ (2 * t) - (3 : ℝ) ^ (2 * t)) • u) = 0 := by
      rw [sub_smul, hsmul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hu)
  have hlogs := congrArg Real.log hpowers
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at hlogs
  have hlogne : Real.log (2 : ℝ) ≠ Real.log (3 : ℝ) := by
    intro h
    have hexp := congrArg Real.exp h
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 3)] at hexp
    norm_num at hexp
  have hmul : (2 * t) * (Real.log (2 : ℝ) - Real.log (3 : ℝ)) = 0 := by
    linear_combination hlogs
  have ht : 2 * t = 0 :=
    (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hlogne)
  linarith

/-- Existence of a nonzero square-matrix central ghost with prime-independent forward and
reflected legs.  No Hermitian, positivity, or invertibility condition is imposed. -/
def PrimeGammaTwoThreeFiniteMatrixCentralGhostWard (n : ℕ) (t : ℝ) : Prop :=
  ∃ G H : Matrix (Fin n) (Fin n) ℂ, G ≠ 0 ∧
    primeGammaCentralModuleGhostWardEquation
      G H t deningerCalderonWittPrimeTwo ∧
    primeGammaCentralModuleGhostWardEquation
      G H t deningerCalderonWittPrimeThree

/-- Every positive matrix rank has a central shared ghost exactly at neutral grade. -/
theorem primeGammaTwoThreeFiniteMatrixCentralGhostWard_iff
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    PrimeGammaTwoThreeFiniteMatrixCentralGhostWard n t ↔ t = 0 := by
  constructor
  · rintro ⟨G, H, hG, htwo, hthree⟩
    exact primeGammaCentralModuleGhost_two_three_rigidity hG t htwo hthree
  · rintro rfl
    let i : Fin n := ⟨0, hn⟩
    let G : Matrix (Fin n) (Fin n) ℂ := fun j k =>
      if j = i ∧ k = i then 1 else 0
    refine ⟨G, G, ?_, ?_, ?_⟩
    · intro hG
      have hentry := congrFun (congrFun hG i) i
      simp [G] at hentry
    · simp [primeGammaCentralModuleGhostWardEquation,
        primeGammaPhysicalRotationDeterminant]
    · simp [primeGammaCentralModuleGhostWardEquation,
        primeGammaPhysicalRotationDeterminant]

/-- Pointwise finite-matrix central-ghost descent on an actual Xi divisor support. -/
def FrankensteinFiniteMatrixCentralGammaGhostDescendsAt
    (n : ℕ) (rho : XiDivisorSupport) : Prop :=
  PrimeGammaTwoThreeFiniteMatrixCentralGhostWard n
    (2 * (rho : ℂ).re - 1)

/-- Universal finite-matrix central-ghost descent over actual Xi support. -/
def EveryFrankensteinFiniteMatrixCentralGammaGhostDescends (n : ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    FrankensteinFiniteMatrixCentralGammaGhostDescendsAt n rho

/-- For every positive matrix rank, universal central-ghost descent is exactly RH. -/
theorem everyFrankensteinFiniteMatrixCentralGammaGhostDescends_iff_riemannHypothesis
    {n : ℕ} (hn : 0 < n) :
    EveryFrankensteinFiniteMatrixCentralGammaGhostDescends n ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => by
      have ht := (primeGammaTwoThreeFiniteMatrixCentralGhostWard_iff hn _).mp (h rho)
      linarith
  · intro h rho
    apply (primeGammaTwoThreeFiniteMatrixCentralGhostWard_iff hn _).mpr
    have hr := xi_divisor_support_re_eq_half_of_rh h rho
    linarith

/-- The same rank-uniform central-ghost law is exactly the shared HB/FZZ-P/PW-B/RBH Ward
endpoint. -/
theorem everyFrankensteinFiniteMatrixCentralGammaGhostDescends_iff_sharedFourRouteWardEndpoint
    {n : ℕ} (hn : 0 < n) :
    EveryFrankensteinFiniteMatrixCentralGammaGhostDescends n ↔
      SharedFourRouteWardEndpoint := by
  have hshared : SharedFourRouteWardEndpoint ↔ RiemannHypothesis :=
    everyFrankensteinChannelResolvedGammaJointNaturality_iff_sharedFourRouteWardEndpoint.symm.trans
      everyFrankensteinChannelResolvedGammaJointNaturality_iff_riemannHypothesis
  exact
    (everyFrankensteinFiniteMatrixCentralGammaGhostDescends_iff_riemannHypothesis hn).trans
      hshared.symm

/-- Closed classification of all positive finite matrix ranks. -/
def SharedWardFiniteMatrixCentralGammaGhostRouteKilled : Prop :=
  ∀ n : ℕ, 0 < n →
    (∀ t : ℝ, PrimeGammaTwoThreeFiniteMatrixCentralGhostWard n t ↔ t = 0) ∧
    (EveryFrankensteinFiniteMatrixCentralGammaGhostDescends n ↔
      SharedFourRouteWardEndpoint) ∧
    (EveryFrankensteinFiniteMatrixCentralGammaGhostDescends n ↔
      RiemannHypothesis)

/-- **[SHARED-WARD ROUTE-CLASS KILL].**  Arbitrary nonzero finite matrix enrichment cannot
manufacture the missing source law while the prime--Gamma rotations remain central and the two
ghost legs remain prime-independent.  At every positive rank the resulting universal law is an
exact HB/FZZ-P/PW-B/RBH and RH receiver. -/
theorem sharedWardFiniteMatrixCentralGammaGhostRouteKilled :
    SharedWardFiniteMatrixCentralGammaGhostRouteKilled := by
  intro n hn
  exact ⟨primeGammaTwoThreeFiniteMatrixCentralGhostWard_iff hn,
    everyFrankensteinFiniteMatrixCentralGammaGhostDescends_iff_sharedFourRouteWardEndpoint hn,
    everyFrankensteinFiniteMatrixCentralGammaGhostDescends_iff_riemannHypothesis hn⟩

end

end RHTower
