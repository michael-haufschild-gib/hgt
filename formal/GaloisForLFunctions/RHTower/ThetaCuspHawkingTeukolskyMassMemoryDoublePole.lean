import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyThermalDealiasingEndpoint

/-!
# Chiral Teukolsky horizon-memory double pole

Let `J₀(omega)` be the normalized Birmingham--Mokhtari plus-branch Jost factor. At each
fundamental resonance it has a simple zero with nonzero derivative `d`. A stationary absorbed-mass
insertion occurs between two copies of the retarded Green function. Its cross-helicity component
therefore has local form

`-B / J₀(omega)^2`,

where `B` is the nonzero scalar-minus-vector mass-variation projection derived in
`ThetaCuspHawkingNonlinearChiralTeukolskyReturnProducer`. Consequently its normalized leading
coefficient is exactly `-B / d^2`.

A direct, transient, or continuum return with one resonant Green factor has form

`N(omega) / J₀(omega)`

with `N` continuous at the resonance. Multiplication by `(omega-omega₀)^2` sends every such term
to zero, so no sum of one-Green terms can cancel the horizon-memory coefficient. This is a
pole-order statement, not positivity or a QNM-completeness assumption.

The resonance pairing is also invariant under an infinitesimal gauge commutator
`deltaL -> deltaL + [L,X]`: left and right null vectors annihilate both commutator terms.

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`

Another nondecaying operator insertion can carry two Green factors, so pole order alone does not
classify every zero-frequency second-order Einstein perturbation. The downstream full-Einstein
grade theorem supplies the missing selection: mass/spin memory has Hermitian grade, while
non-self-dual quadratic terms have mixed or anti-chiral grade, so none is a same-grade counterterm
to the holomorphic Plebanski carrier.

There is also a strict cusp-weight separation. Absorbed mass is Hermitian quadratic, so a linear
weight `s` produces memory weight `s + conj(s)` and cubic return weight `2s + conj(s)`. This never
equals the holomorphic quadratic weight `2s` at an Xi divisor. Thus horizon memory cannot supply
the still-missing doubled-weight vacuum Teukolsky source, despite its protected double pole.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Left/right resonance pairing kills every infinitesimal operator-gauge commutator. -/
theorem teukolskyResonantOperatorInsertion_gaugeInvariant
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L deltaL X : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ) (psi : V)
    (hright : L psi = 0) (hleft : ∀ v, ell (L v) = 0) :
    ell ((deltaL + L.comp X - X.comp L) psi) = ell (deltaL psi) := by
  simp [hleft, hright]

/-- Green function of the normalized plus-branch reciprocal-Gamma Jost factor. -/
def d4FundamentalQNMNormalizedPlusGreen (z omega : ℂ) : ℂ :=
  (thetaCuspHawkingHypergeometricJostPlus omega z)⁻¹

/-- Exact residue of the normalized Green function at every plus-branch resonance. -/
theorem d4FundamentalQNMNormalizedPlusGreen_tendsto_residue (n : ℕ) (z : ℂ) :
    Tendsto
      (fun omega : ℂ =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) *
          d4FundamentalQNMNormalizedPlusGreen z omega)
      (𝓝[≠] (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z))
      (𝓝 (teukolskyNormalizedJostOmegaDerivative n)⁻¹) := by
  let sigma := thetaCuspHawkingTopologicalBlackHoleQNMPlus n z
  let D : ℂ → ℂ := fun omega => thetaCuspHawkingHypergeometricJostPlus omega z
  let N : ℂ → ℂ := fun _ => 1
  have hD : HasDerivAt D (teukolskyNormalizedJostOmegaDerivative n) sigma := by
    simpa [D, sigma, teukolskyNormalizedJostOmegaDerivative] using
      thetaCuspHawkingHypergeometricHasDerivAt_jostPlus_qnm n z
  have hD0 : D sigma = 0 := by
    simp [D, sigma, thetaCuspHawkingHypergeometricJostPlus_qnm_zero]
  have hlim := tendsto_residue_of_simple_zero hD hD0
    (teukolskyNormalizedJostOmegaDerivative_ne_zero n)
    (continuousAt_const : ContinuousAt N sigma)
  simpa [sigma, D, N, d4FundamentalQNMNormalizedPlusGreen,
    div_eq_mul_inv] using hlim

/-- Leading Laurent coefficient of the chiral stationary mass-memory insertion. -/
def d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient
    (amplitude z : ℂ) : ℂ :=
  -d4FundamentalQNMNonlinearChiralSource amplitude z *
    (teukolskyNormalizedJostOmegaDerivative 0)⁻¹ ^ 2

/-- Horizon-memory double-pole coefficient is theta-shadow even. -/
theorem d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient_shadow
    (amplitude z : ℂ) :
    d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient amplitude
        (thetaCuspHawkingOpticalCuspShadow z) =
      d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient amplitude z := by
  unfold d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient
  rw [d4FundamentalQNMNonlinearChiralSource_shadow]

/-- At every Xi descendant the double-pole coefficient is nonzero exactly for nonzero absorbed
seed amplitude. -/
theorem d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient_xi_ne_zero_iff
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient amplitude
        (xiSpectralPoint q) ≠ 0 ↔
      amplitude ≠ 0 := by
  unfold d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient
  rw [mul_ne_zero_iff]
  constructor
  · rintro ⟨hsource, -⟩
    exact (d4FundamentalQNMNonlinearChiralSource_xi_ne_zero_iff amplitude q).mp
      (neg_ne_zero.mp hsource)
  · intro ha
    exact ⟨neg_ne_zero.mpr
        ((d4FundamentalQNMNonlinearChiralSource_xi_ne_zero_iff amplitude q).mpr ha),
      pow_ne_zero 2 (inv_ne_zero (teukolskyNormalizedJostOmegaDerivative_ne_zero 0))⟩

/-- Two-Green stationary mass-memory contribution to the chiral response. -/
def d4ThetaTeukolskyChiralMassMemoryGreenInsertion
    (amplitude z omega : ℂ) : ℂ :=
  -d4FundamentalQNMNonlinearChiralSource amplitude z *
    d4FundamentalQNMNormalizedPlusGreen z omega ^ 2

/-- Mass-memory insertion plus an arbitrary one-Green source return. -/
def d4ThetaTeukolskyChiralMassMemoryOneGreenCompletion
    (amplitude z : ℂ) (directNumerator : ℂ → ℂ) (omega : ℂ) : ℂ :=
  d4ThetaTeukolskyChiralMassMemoryGreenInsertion amplitude z omega +
    directNumerator omega * d4FundamentalQNMNormalizedPlusGreen z omega

/-- Exact pole-order separation. Every continuous one-Green numerator disappears at double-pole
grade, leaving only the stationary horizon-memory coefficient. -/
theorem d4ThetaTeukolskyChiralMassMemoryOneGreenCompletion_tendsto_doublePoleCoefficient
    (amplitude : ℂ) (q : XiZeroCopy) (directNumerator : ℂ → ℂ)
    (hN : ContinuousAt directNumerator
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))) :
    Tendsto
      (fun omega : ℂ =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMPlus 0
            (xiSpectralPoint q)) ^ 2 *
          d4ThetaTeukolskyChiralMassMemoryOneGreenCompletion
            amplitude (xiSpectralPoint q) directNumerator omega)
      (𝓝[≠] (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)))
      (𝓝 (d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient
        amplitude (xiSpectralPoint q))) := by
  let sigma := thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)
  let x : ℂ → ℂ := fun omega => omega - sigma
  let G : ℂ → ℂ := fun omega =>
    d4FundamentalQNMNormalizedPlusGreen (xiSpectralPoint q) omega
  have hx : Tendsto x (𝓝[≠] sigma) (𝓝 0) := by
    have hid : Tendsto (fun omega : ℂ => omega) (𝓝[≠] sigma) (𝓝 sigma) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    have hc : Tendsto (fun _ : ℂ => sigma) (𝓝[≠] sigma) (𝓝 sigma) :=
      tendsto_const_nhds
    simpa only [x, sub_self] using hid.sub hc
  have hG : Tendsto (fun omega => x omega * G omega) (𝓝[≠] sigma)
      (𝓝 (teukolskyNormalizedJostOmegaDerivative 0)⁻¹) := by
    simpa [x, G, sigma] using
      d4FundamentalQNMNormalizedPlusGreen_tendsto_residue 0 (xiSpectralPoint q)
  have hNr : Tendsto directNumerator (𝓝[≠] sigma)
      (𝓝 (directNumerator sigma)) :=
    hN.tendsto.mono_left nhdsWithin_le_nhds
  have hmemory : Tendsto
      (fun omega => x omega ^ 2 *
        d4ThetaTeukolskyChiralMassMemoryGreenInsertion
          amplitude (xiSpectralPoint q) omega)
      (𝓝[≠] sigma)
      (𝓝 (d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient
        amplitude (xiSpectralPoint q))) := by
    have h := (hG.pow 2).const_mul
      (-d4FundamentalQNMNonlinearChiralSource amplitude (xiSpectralPoint q))
    convert h using 1
    · funext omega
      simp [d4ThetaTeukolskyChiralMassMemoryGreenInsertion, x, G]
      ring
    · simp [d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient]
  have honeGreen : Tendsto
      (fun omega => x omega ^ 2 * (directNumerator omega * G omega))
      (𝓝[≠] sigma) (𝓝 0) := by
    have h := hx.mul (hG.mul hNr)
    convert h using 1
    · funext omega
      ring
    · ring
  have hsum := hmemory.add honeGreen
  convert hsum using 1
  · funext omega
    simp only [d4ThetaTeukolskyChiralMassMemoryOneGreenCompletion, x, G, sigma]
    ring
  · simp

/-- No continuous one-Green completion can erase the nonzero memory double pole. -/
theorem d4ThetaTeukolskyChiralMassMemoryOneGreenCompletion_cannot_cancel
    (amplitude : ℂ) (q : XiZeroCopy) (directNumerator : ℂ → ℂ)
    (ha : amplitude ≠ 0)
    (hN : ContinuousAt directNumerator
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q))) :
    ¬ Tendsto
      (fun omega : ℂ =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMPlus 0
            (xiSpectralPoint q)) ^ 2 *
          d4ThetaTeukolskyChiralMassMemoryOneGreenCompletion
            amplitude (xiSpectralPoint q) directNumerator omega)
      (𝓝[≠] (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q)))
      (𝓝 0) := by
  intro hzero
  have hcoefficient :=
    d4ThetaTeukolskyChiralMassMemoryOneGreenCompletion_tendsto_doublePoleCoefficient
      amplitude q directNumerator hN
  have heq :
      d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient
        amplitude (xiSpectralPoint q) = 0 :=
    tendsto_nhds_unique hcoefficient hzero
  exact
    (d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient_xi_ne_zero_iff
      amplitude q).mpr ha heq

/-- Nonzero horizon absorption activates the memory double pole in every Xi sector. Hence this
coefficient is a source producer, but its shadow-even support does not itself select RH. -/
theorem d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient_nonzero_everyXi
    {amplitude : ℂ} (ha : amplitude ≠ 0) :
    ∀ q : XiZeroCopy,
      d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient amplitude
        (xiSpectralPoint q) ≠ 0 := by
  intro q
  exact
    (d4ThetaTeukolskyChiralMassMemoryDoublePoleCoefficient_xi_ne_zero_iff
      amplitude q).mpr ha

/-! ## Hermitian memory and holomorphic quadratic weight are different sectors -/

/-- Cusp weight of the Hermitian quadratic horizon mass `A * conj(A)`. -/
def d4ThetaTeukolskyHermitianHorizonMemoryCuspWeight (z : ℂ) : ℂ :=
  d4ThetaTeukolskyLinearCuspWeight z +
    star (d4ThetaTeukolskyLinearCuspWeight z)

/-- Cusp weight of the cubic returned field `A * |A|^2`. -/
def d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight (z : ℂ) : ℂ :=
  d4ThetaTeukolskyLinearCuspWeight z +
    d4ThetaTeukolskyHermitianHorizonMemoryCuspWeight z

theorem d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight_eq (z : ℂ) :
    d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight z =
      2 * d4ThetaTeukolskyLinearCuspWeight z +
        star (d4ThetaTeukolskyLinearCuspWeight z) := by
  unfold d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight
    d4ThetaTeukolskyHermitianHorizonMemoryCuspWeight
  ring

private lemma d4ThetaTeukolskyLinearCuspWeight_xi_ne_zero (q : XiZeroCopy) :
    d4ThetaTeukolskyLinearCuspWeight (xiSpectralPoint q) ≠ 0 := by
  rw [d4ThetaTeukolskyLinearCuspWeight_eq_half_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  apply div_ne_zero
  · intro h
    have hs := xi_divisor_support_re_mem_open_unit q.1
    rw [h] at hs
    norm_num at hs
  · norm_num

/-- Hermitian horizon memory cannot masquerade as the holomorphic doubled-weight Teukolsky
source at any Xi divisor. -/
theorem d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight_ne_quadraticChiral
    (q : XiZeroCopy) :
    d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight (xiSpectralPoint q) ≠
      d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q) := by
  rw [d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight_eq,
    d4ThetaTeukolskyQuadraticChiralCuspWeight]
  intro h
  have hstar : star (d4ThetaTeukolskyLinearCuspWeight (xiSpectralPoint q)) = 0 := by
    linear_combination h
  have hs := congrArg star hstar
  simp at hs
  exact d4ThetaTeukolskyLinearCuspWeight_xi_ne_zero q hs

end

end RHTower
