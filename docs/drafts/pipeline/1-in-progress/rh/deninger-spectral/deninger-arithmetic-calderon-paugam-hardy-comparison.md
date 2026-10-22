# Arithmetic Calderón--Paugam Hardy comparison

- **ID:** `deninger-arithmetic-calderon-paugam-hardy-comparison`
- **Stage:** 1-in-progress
- **Type:** RH-BEARING SOURCE CONJECTURE
- **Label:** `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`
- **Parent:** `deninger-arithmetic-calderon-green-intermediate-extension`
- **Statement:** the global source Calderón polarization descends to a
  closed nuclear Hardy relation, represented by projectors modulo the
  nuclear trace ideal; positive Hodge completion makes it an exact
  orthogonal splitting whose discrete comparison is Paugam's
  upper/lower trace sector.  Consequently the Green cup is Paugam's
  pairing and its Hodge rotation is positive.

## Forced local projectors

For a finite nonconstant Kummer packet let
\[
 S_\ell=\operatorname{sgn}(D_\ell),\qquad
 W_\ell=iS_\ell.
\]
The proved local Calderón domain has complementary Hardy projectors
\[
 \Pi_{\ell,+}=\frac{1+S_\ell}{2}
             =\frac{1-iW_\ell}{2},
 \qquad
 \Pi_{\ell,-}=\frac{1-S_\ell}{2}
             =\frac{1+iW_\ell}{2}.                              \tag{1}
\]
Complex conjugation exchanges `(1)`.  The anti-linear local Hodge
operator
\[
 \mathfrak C_\ell=W_\ell c
\]
satisfies \(\mathfrak C_\ell^2=-1\), and the local Green cup followed
by \(\mathfrak C_\ell\) is the positive Dirichlet energy.

At prime and real boundary strata, the extended-cusp and
orientation-sign domains provide the corresponding two boundary
polarizations.

## Conjecture

`[CONJECTURE] [DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON]`

The global arithmetic intermediate extension has a closed
polarization relation
\[
 \mathcal L_{\mathrm{Cal}}
 \subset
 \mathcal E^1_{\mathrm{arith}}
 \oplus(\mathcal E^1_{\mathrm{arith}})'                         \tag{2}
\]
with the following properties.

1. **Finite strict Hardy splitting.**
   On every finite field/place/lattice packet, `(1)` and the
   prime/real analogues give exact complementary projectors
   \[
   \Pi_{\pm,\alpha}^2=\Pi_{\pm,\alpha},\qquad
   \Pi_{+,\alpha}\Pi_{-,\alpha}=0,\qquad
   \Pi_{+,\alpha}+\Pi_{-,\alpha}=1.                             \tag{3}
   \]
   They preserve every finite Milnor incidence and residue attaching
   map.

2. **Nuclear source polarization.**
   The finite relations assemble to `(2)`.  On the nuclear source it
   is represented by the two Poisson embeddings and almost-sections
   of `DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR`.  For every
   convolution test packet, the failure of complementary
   idempotence lies in the nuclear trace ideal.  No complemented-range
   assertion for Meyer's \(H_+\) embedding is assumed.

3. **Source construction.**  Relation `(2)` is obtained by gluing
   local Calderón data through the full Milnor relative Sullivan
   incidence and the common Poisson/Fourier correction
   \[
   M_\phi-ZM_\phi Z^{-1},\qquad
   M_\phi-\mathcal F\mathcal J
                 M_\phi\mathcal J\mathcal F,                    \tag{4}
   \]
   not by listing zeta zeros.  Changing \(\phi\) changes its
   almost-projector representative by a chain-null nuclear
   commutator and leaves cohomology,
   cup, and trace unchanged.

4. **Exact Hodge completion.**  The global Dirichlet form obtained
   from `(2)` is closable and positive on reduced arithmetic
   cohomology.  Its Hilbert completion
   \(\mathcal H^1_{\mathrm{arith}}\) carries exact complementary
   orthogonal projectors
   \[
   \Pi_+,\Pi_-:\mathcal H^1_{\mathrm{arith}}
   \longrightarrow\mathcal H^1_{\mathrm{arith}}.
   \]
   Their restrictions have the finite local values `(3)`.  Exact
   projectors are asserted here, after positive completion, not on
   the uncomplemented nuclear source.  Concretely, the closed source
   relation supplies a bounded self-adjoint almost-involution \(S\)
   with \(S^2-1\) nuclear.  Source geometry proves \(\ker S=0\);
   self-adjoint Fredholmness then makes \(S\) invertible, and
   `DAC_POLAR_SIGN_LIFT_NUCLEAR_ALMOST_PROJECTOR` defines
   \[
     C=S|S|^{-1},\qquad \Pi_\pm=(1\pm C)/2.
   \]
   Thus exact projectors are constructed canonically; they are not
   postulated from a zero-sector splitting.

5. **Paugam sector comparison.**  Let
   \[
   U:H^1_{\mathrm{arith}}\xrightarrow{\sim}M_\zeta
   \]
   be the strict nuclear Poisson comparison.  After applying Paugam's
   discrete-spectral functor, the completed projectors \(\Pi_\pm\)
   give an admissible upper/lower generalized spectral splitting.
   This resolves the noncanonical discrete choice by source
   Calderón data without asserting a continuous splitting of the
   Fréchet quotient itself.

6. **Green--trace equality.**  Write
   \(\mathcal JF(x)=x^{-1}F(x^{-1})\) for Paugam's reflection.  For
   source test packets represented by \(F,G\),
   \[
   \begin{aligned}
   \Psi_{\mathrm{Green}}([F],[G])
   &=
   \operatorname{Tr}\!\left(
     F*\mathcal JG-G*\mathcal JF
     \,\middle|\,
     \Pi_+\mathcal H^1_{\mathrm{arith}}
   \right)\\
   &=
   \psi_{\mathrm{Paugam}}(U[F],U[G]).                            \tag{5}
   \end{aligned}
   \]
   The first equality follows on the nuclear core by
   `DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION`, the global Green formula,
   and hereditary nuclear trace; it is then extended by strict
   continuity.  No spectral-point evaluation occurs in this proof.

7. **Positive Hodge rotation.**  The local
   \(\mathfrak C_\ell\) and prime/real exchange maps glue to an
   anti-linear
   \[
   \mathfrak C:H^1_{\mathrm{arith}}\to H^1_{\mathrm{arith}},
   \qquad \mathfrak C^2=-1,                                    \tag{6}
   \]
   commuting with the source flow.  For every nonzero nuclear class,
   \[
   \Psi_{\mathrm{Green}}(x,\mathfrak Cx)
   =
   \mathcal E_{\mathrm{Dir}}(x)>0.                              \tag{7}
   \]
   Its completion defines the Hodge Hilbert space.  Equation `(5)`
   transports `(7)` to Paugam's alternating form; positivity is proved
   geometrically, not imported from Paugam's RH-conditional spectral
   formula.

8. **Hodge--Schwartz resolvent faithfulness.**  The smooth arithmetic
   Hodge core is dense in \(M_\zeta\) for its nuclear quotient topology
   and is preserved by every off-axis resolvent of
   \(\Theta-\tfrac12\).  Alternatively, it is enough that centered
   time one \(V=\exp(\Theta_{\mathcal H}-\tfrac12)\) satisfy
   \[
     V-c:\mathcal D_{\mathrm{Hdg}}\to\mathcal D_{\mathrm{Hdg}}
     \quad\text{surjectively whenever }|c|\ne1.
   \]
   Every nonzero Meyer strong-dual eigenfunctional restricts
   nontrivially to this core.  By
   `DAC_DENSE_RESOLVENT_TRANSPOSE_PURITY`, the corresponding
   eigencharacter has unit modulus, forcing
   \(\operatorname{Re}\rho=\tfrac12\).  This treats all generalized
   Mellin jets.  Hodge-bounded Riesz representation and
   `DAC_UNITARY_FLOW_RIESZ_EIGENFUNCTIONAL_PURITY` remain a stronger
   sufficient alternative.

## Why this is the exact RH gate

Paugam proves unconditionally that \(\psi_{\mathrm{Paugam}}\) is
alternating, nondegenerate, and weight one.  He proves positivity of
his spectral sign-conjugation form only under RH.  Therefore his
positivity statement cannot be used as input.

Clauses 1--7 reverse the implication: source Calderón energy proves
positivity first, while `(5)` proves that the same positive form
polarizes the actual Meyer quotient.  Weight-one cup compatibility
then makes
\[
 \Theta-\tfrac12
\]
skew-adjoint on the completed \(H^1\).  Clause 6 ensures this statement
is the cup comparison for the actual Meyer quotient, and clause 8
ensures it sees every generalized zeta-zero functional.  Meyer's
spectral theorem
then yields RH, including exclusion of off-line generalized blocks.

## Downstream subgate: source Calderón orientation before scalar trace

Arithmetic carrier and additive Poisson comparison are no longer conjectural.  Pro-Stein residue
fibre is strictly represented by

\[
 C^0=\mathbb C\oplus H_\cap,
 \qquad C^1=H_-\oplus P_{\mathbb Q},
 \qquad C^2=D_{\mathrm{Ar},\mathbb Q},
\]

with `H^1=M_zeta`.  This does not yet provide global source Hodge domain or oriented trace.

Former first subgate `DAC_RELEVANT_GREEN_PAUGAM_CHAIN_TRANSGRESSION` is retired.  It postulated a
scalar `Omega_Meyer/Paugam` on raw Poisson--zeta cochains before a Hardy sector existed.  Paugam's
number-field formula is instead

\[
 \psi(F,G)=
 \operatorname{Tr}\!\left(F*JG-G*JF\mid H^1_{d,+}\right),     \tag{8}
\]

after discrete spectral suspension and choice of one conjugation-exchanged half.  Meyer's cutoff
corrections compute full virtual character and do not construct (H^1_{d,+}).

This distinction is forced.  At a reflection pair put

\[
 A_\rho(F,G)=
 \widehat F(\rho)\widehat G(1-\rho)
 -\widehat G(\rho)\widehat F(1-\rho).
\]

Then (A_{1-\rho}=-A_\rho).  Hence reflection-complete Meyer trace of this integrand is zero,
whereas Paugam's oriented half-trace `(8)` is nondegenerate.  Swapping halves negates `(8)`, so no
nonzero scalar pairing descends from unoriented raw complex.  Full proof and positive survivor are
recorded in `../../../5-failed/deninger-relevant-green-paugam-chain-transgression.md`.

This card is no longer the first Route-L source gate. Critical Floquet subtraction is exactly the
von Mangoldt current but is diagonally indefinite, while actual Gamma/co-Poisson Green transport
and Calderón--Witt incidence are already constructed and nonselective. The upstream gate is the
strict cofinal Euler--Gamma/Möbius gauge defect and its non-diagonal unsquared Green--Stokes
annihilation. Once that source theorem induces corrected Tate--Floquet/Möbius Poisson descent, the
remaining orientation chain is:

1. glue local Kummer, prime-cusp, and real-apex Calderón data through every Tate--Milnor and
   residue/corestriction attachment to a closed global Lagrangian relation;
2. construct its Hodge-symmetric nuclear almost-involution (S), with (S^2-1) nuclear;
3. prove `DAC_GLOBAL_GREEN_ENERGY_RADICAL` and resulting
   `DAC_ARITHMETIC_CALDERON_GLOBAL_CHIRALITY_KERNEL`, so (C=S|S|^{-1}) and
   \(\Pi_\pm=(1\pm C)/2\) exist;
4. define oriented source trace
   \[
     \Omega_C(F,G)=
     \operatorname{Tr}\!\left(
       \Pi_+\lambda(F*JG-G*JF)
     \right)                                                  \tag{9}
   \]
   and prove its discrete comparison with `(8)`.

Before step 3, an orientation-twisted Real relative trace class attached to closed relation is a correctly
typed intermediate target; it is not yet a scalar Paugam pairing.  Full-packet Cauchy/Bessel
conservativity remains one optional proof of energy radical, not definition of source object.
After `(9)`, remaining analytic gate is `DAC_ARITHMETIC_HODGE_SCHWARTZ_RESOLVENT_CORE`.

## Exact proof program

1. Construct finite field/place/lattice Calderón projectors and prove
   compatibility with every relative Sullivan attaching map.
2. Show the positive finite Hodge--Koszul contractions commute with
   `(1)` and with residue/corestriction.
3. Assemble the closed relation `(2)` on the strict nuclear
   inductive/projective system.  Identify its cutoff representatives
   with Meyer's almost-sections; do not require complemented range.
4. Prove closability and positivity of the global Dirichlet form and
   prove kernel vanishing for the self-adjoint global Calderón
   almost-involution.  Its nuclear defect then supplies Fredholm
   coercivity.  Apply
   `DAC_POLAR_SIGN_LIFT_NUCLEAR_ALMOST_PROJECTOR` to construct exact
   projectors only on the Hilbert completion.
   Kernel vanishing is
   `DAC_ARITHMETIC_CALDERON_GLOBAL_CHIRALITY_KERNEL`.
5. Identify the global relative polarization with the Toeplitz pair
   `(4)`.
6. Apply Meyer's nuclear heredity theorem to compute the quotient trace
   and prove `(5)` for compactly supported convolution packets.
7. Extend `(5)` to the full relevant nuclear core by factorization and
   bounded-set uniform nuclearity.
8. Glue the local anti-linear Hodge exchanges and prove `(7)` by the
   global Dirichlet decomposition.
9. Prove strict transpose injectivity on the generalized-spectral
   filtration.

## Falsifiers

- A local projector that fails a Milnor or residue attaching map blocks
  global descent.
- Closed range is not complemented range.  Meyer's positive embedding
  has no proved continuous section, so a strict projector on the
  nuclear source may not be assumed.
- Finite-packet compatibility without a closed global relation and
  nuclear almost-section estimates does not define `(2)`.
- Nuclear almost-idempotence without Hodge self-adjointness and
  global middle-kernel vanishing does not produce exact projectors.
- An upper/lower splitting chosen from a zero list is circular and does
  not satisfy clause 2.
- Toeplitz trace alone does not prove `(5)`; hereditary passage to the
  arithmetic quotient and matching of relative polarizations are
  mandatory.
- Paugam's RH-conditional positivity cannot be cited for `(7)`.
- Density of \(U\) without strong-dual jet faithfulness is
  insufficient.
- Hilbert-space resolvent existence alone is insufficient.  The
  resolvent must preserve a core dense in the nuclear Meyer topology,
  so every nonzero strong-dual functional restricts nontrivially.
- The existing
  `DeningerArithmeticSourceGreen.lean` uses the zero-indexed
  `XiDivisorL2` carrier.  It is a frozen comparison realization and
  cannot construct `(2)`, `(6)`, or `(7)` without circularly importing
  the target divisor.
- No CCM object participates.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, arXiv:math/0412277.
- Frederic Paugam, *Spectral symmetries of zeta functions*,
  arXiv:0803.0199.
- `DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION`.
- `DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR`.
- `DAC_DENSE_RESOLVENT_TRANSPOSE_PURITY`.
- `DAC_ARITHMETIC_HODGE_SCHWARTZ_RESOLVENT_CORE`.
- `DAC_ARITHMETIC_CALDERON_GLOBAL_CHIRALITY_KERNEL`.
- `DAC_POLAR_SIGN_LIFT_NUCLEAR_ALMOST_PROJECTOR`.
- `DAC_UNITARY_FLOW_RIESZ_EIGENFUNCTIONAL_PURITY`.
- `DAC_RIESZ_EIGENFUNCTIONAL_HODGE_PURITY`.
- `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`.
- `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`.

## Log

- 2026-07-27 — Replaced the vague cup-isometry/positivity gap by a
  single source polarization comparison: the global Calderón relation
  must give Meyer's nuclear relative trace and become Paugam's
  upper/lower splitting only after positive Hodge completion, with
  Green energy providing positivity before spectral evaluation.
- 2026-07-27 — Replaced the stronger generator-domain spectral gate
  by bounded nonzero order-zero evaluation plus centered time-one
  unitarity.  Higher jets are no longer needed for RH itself.
- 2026-07-27 — Improved the gate again to a dense nuclear
  Hodge--Schwartz core preserved by off-axis resolvents.  This acts
  directly on Meyer's strong-dual jets and removes pointwise
  Hilbert-boundedness from the minimal hypothesis.
- 2026-08-08 — Retired pre-sector scalar chain transgression.  Primary Meyer/Paugam formulas and
  reflection-pair cancellation show full Meyer character annihilates Paugam wedge.  Reordered
  dependency through global source Calderón relation, Green-radical/chirality-kernel exactness,
  polar-sign Hardy orientation, and only then scalar Paugam trace comparison.
