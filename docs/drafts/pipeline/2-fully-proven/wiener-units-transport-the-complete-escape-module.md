# Wiener units transport the complete escape module

- **ID:** wiener-units-transport-the-complete-escape-module
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
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

The exact source convolution, bounded correction, unit identification, and
all first-coordinate Wiener covariance limits are already proved in the
corpus. The double covariance limit and exact complete-source pairing identity
passed Lean with standard axioms and final source checks. The unit-twisted Gram
unitary and dilation intertwining passed in scratch. Normalization and source
energy ratio are queued; exact real convolution comparison, full action
transport, and the actual Möbius--Liouville specialization are drafted but
unchecked. No full unit-transport theorem is yet claimed as formalized.

## Gates

- [x] Dependency-closed paper proof.
- [x] Full Wiener pairing convergence in Lean.
- [ ] Unit-twisted cyclic realization and exact source Gram comparison.
- [ ] Möbius--Liouville specialization, transitive axiom audits, source checks.
