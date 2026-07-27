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
   the uncomplemented nuclear source.

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

8. **Riesz spectral faithfulness.**  For every nontrivial zeta zero,
   the order-zero Meyer evaluation functional pulled back by \(U\) is
   bounded for the Hodge norm, has a nonzero Riesz representative in
   \(\operatorname{Dom}\Theta_{\mathcal H}\), and its transpose action
   is the corresponding eigencharacter.  By
   `DAC_RIESZ_EIGENFUNCTIONAL_HODGE_PURITY`, this is the exact
   one-way comparison required for RH.  The stronger version retains
   every finite-order generalized Mellin jet, its domain filtration,
   and block multiplicity.

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

## Exact proof program

1. Construct finite field/place/lattice Calderón projectors and prove
   compatibility with every relative Sullivan attaching map.
2. Show the positive finite Hodge--Koszul contractions commute with
   `(1)` and with residue/corestriction.
3. Assemble the closed relation `(2)` on the strict nuclear
   inductive/projective system.  Identify its cutoff representatives
   with Meyer's almost-sections; do not require complemented range.
4. Prove closability and positivity of the global Dirichlet form and
   construct the exact projectors only on its Hilbert completion.
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
- An upper/lower splitting chosen from a zero list is circular and does
  not satisfy clause 2.
- Toeplitz trace alone does not prove `(5)`; hereditary passage to the
  arithmetic quotient and matching of relative polarizations are
  mandatory.
- Paugam's RH-conditional positivity cannot be cited for `(7)`.
- Density of \(U\) without strong-dual jet faithfulness is
  insufficient.
- Membership in the nuclear strong dual is also insufficient.  The
  order-zero Meyer functionals must be Hodge-norm bounded with Riesz
  representatives in the generator domain.
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
- `DAC_RIESZ_EIGENFUNCTIONAL_HODGE_PURITY`.
- `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`.
- `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`.

## Log

- 2026-07-27 — Replaced the vague cup-isometry/positivity gap by a
  single source polarization comparison: the global Calderón relation
  must give Meyer's nuclear relative trace and become Paugam's
  upper/lower splitting only after positive Hodge completion, with
  Green energy providing positivity before spectral evaluation.
