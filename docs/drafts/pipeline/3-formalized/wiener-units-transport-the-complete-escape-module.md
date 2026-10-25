# Wiener units transport the complete escape module

- **ID:** wiener-units-transport-the-complete-escape-module
- **Stage:** 3-formalized
- **Type:** LEAN THEOREM
- **Source:** Q-III; exact prefix convolution; full Wiener covariance convergence;
  `UnitsOfTheWienerMonoidPreservePayment.lean` and
  `AnIndexFormulaForTheActualReceiver.lean`.
- **Statement:** Along any actual escaping common Gram subsequence, convolution
  by a real critical Wiener unit produces the same Hilbert module with a new
  nonzero cyclic vector and a scalar normalization. The module annihilator,
  hull, finite dimension, and algebraic quotient index are unchanged.

## Complete paper proof

Write `A` for the actual centered receiver and `E_T` for its pronic energy.
For any complex critical Wiener coefficients `a`, form the finite-cell row
`D_a A(n)=sum_(j<=n) a_j A(floor(n/j))`. Sharp pronic dilation and the triangle
inequality give `||D_a A||_T <= ||a||_W sqrt(E_T)`, treating complex rows in
the complex pronic Hilbert norm. This bound also holds for coefficient tails.

For finite coefficient packets, common Gram convergence gives

`<D_a A,D_b A>_T/E_T -> <pi(a)v,pi(b)v>`.

Approximate both coefficients in Wiener norm by finite packets. The uniform
norm bound controls the difference of the pairings independently of the
horizon. The same estimate holds in the limiting module by contractivity of
`pi`. Thus the displayed limit holds for all Wiener coefficients, with no
assumption that a truncation of a paid kernel is paid.

Let `g` be a real critical Wiener unit, `c` the actual source, and `B` the
centered receiver of `g*c`. The proved convolution identity gives

`B=D_g A + m_c A_g`,

where `A_g` has bounded global pronic norm. All its fixed dilates do as well.
On escape this paid correction disappears in the normalized pairings.
Write `w=pi(g)v`. Invertibility gives `w != 0`; indeed
`v=pi(g^-1)w`. The complete Wiener orbit of `w` equals that of `v`, because
multiplication by `g` permutes the Wiener algebra. Thus `w` is cyclic in the
same Hilbert space. In particular `b=||w||^2>0`.

Full Wiener pairing convergence gives `E_T(B)/E_T(A)->b`. For each fixed
`j,k`, the normalized Gram table of `B` along the same horizons therefore
converges to

`<V_k w,V_j w>/b`.

The Gram realization of this kernel is isometrically equivalent to the
original Hilbert space, sending its `j`th vector to `V_j w/sqrt(b)`. Totality
and the Gram identity prove this equivalence, and the formula intertwines
every dilation. Hence it intertwines the full Wiener action. Its annihilator
and both spectral hulls are exactly the original ones, and all module and
quotient dimensions agree.

This argument also works for any source whose common limiting module and
uniform Wiener action bound have been proved; no analytic source input is
hidden in that generalization.

## Actual cross-programme application

The corpus proves that damped Möbius and damped Liouville sources are related
by the real critical Wiener unit `1_square(n)n^(-epsilon)`, with inverse the
square-dilated damped Möbius kernel. The preceding argument therefore upgrades
their proved equality of paid ideals and obstruction hulls to equivalence of
their actual escape modules, along corresponding horizon subsequences.
The cyclic vectors and normalized Gram kernels can change; the represented
module does not.

## Lean status

Full Wiener pairing convergence, exact source-row dilation and abstract unit
conjugacy have passed canonical source checks and transitive axiom audits.
The complete actual real convolution theorem, positive source-energy ratio,
preservation of escape and Möbius–Liouville specialization passed their final
canonical source-only checks. All transitive axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. Their canonical leaves are
installed and umbrella-wired.

Canonical source application leaves:
- `ArithmeticDefectRigidity/PaidCorrectionsPreserveNormalizedCofactorGrams.lean`
- `ArithmeticDefectRigidity/RealWienerConvolutionTransportsCofactorGrams.lean`
- `ArithmeticDefectRigidity/TheMoebiusAndLiouvilleCofactorModulesAreUnitEquivalent.lean`

The actual application declarations in `ActualCofactorLimit` include
`unit_source_energy_ratio_tendsto`, `wienerUnitSourceGram_tendsto`,
`admits_or_real_unit_convolution_gram_tendsto`,
`admits_or_real_unit_convolution_energy_ratio_tendsto`,
`admits_or_real_unit_convolution_escapes`, and
`admits_or_liouville_gram_is_unit_transport`. The abstract unitary equivalence
and full Wiener intertwining are in `WienerUnitsTransportCofactorGrams`.

## Gates

- [x] Dependency-closed paper proof.
- [x] Full Wiener pairing convergence in Lean.
- [x] Unit-twisted cyclic realization and exact source Gram comparison in scratch.
- [x] Möbius–Liouville specialization and transitive scratch axiom audit.
- [x] Final canonical source checks and transitive axiom audits for the actual convolution applications.
