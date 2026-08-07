# Relevant-complex Green--Paugam scalar chain transgression

- **ID:** `deninger-relevant-green-paugam-chain-transgression`
- **Stage:** 5-failed
- **Former label:** `DAC_RELEVANT_GREEN_PAUGAM_CHAIN_TRANSGRESSION`
- **Type:** ILL-TYPED SOURCE CONJECTURE; POSITIVE ORIENTED SURVIVOR
- **Parent:** `deninger-arithmetic-calderon-paugam-hardy-comparison`
- **Verdict:** proposed orientation-free scalar target cocycle is not defined by raw
  Poisson--zeta cochain data.  Meyer's full character cancels, rather than constructs, Paugam's
  reflection-odd wedge.  Scalar comparison requires an added source Hardy orientation.

## Retired statement

The retired conjecture postulated a scalar cochain cocycle
`Omega_Meyer/Paugam` on the three-term Poisson--zeta complex and a nuclear transgression

```text
Omega_geom - Phi^*(Omega_Meyer/Paugam) = d_Hom T
```

before any spectral or Hardy decomposition.  No such target cocycle is supplied by Meyer or
Paugam.

Paugam's scalar number-field pairing is

\[
 \psi(F,G)=
 \operatorname{Tr}\!\left(
 F*JG-G*JF\mid H^1_{d,+}
 \right),                                                     \tag{1}
\]

where (H^1_{d,+}) is one oriented half of the discrete spectral suspension.  His preceding
supertrace is defined only after a noncanonical decomposition exchanged by conjugation, and its
pre-scalar output is a class in Paugam's \(\mathbb L/c\) quotient.  Neither object is a
degreewise scalar cocycle on raw (C^\bullet_{\mathrm{PZ}}).

Meyer's cutoff operators

\[
 M_\phi-ZM_\phi Z^{-1},\qquad
 M_\phi-\mathcal FJ M_\phi J\mathcal F                     \tag{2}
\]

compute the full virtual character.  They provide no projector onto (H^1_{d,+}).

## Exact cancellation no-go

For a reflection pair \(\rho\leftrightarrow1-\rho\), put

\[
 A_\rho(F,G)=
 \widehat F(\rho)\widehat G(1-\rho)
 -\widehat G(\rho)\widehat F(1-\rho).                        \tag{3}
\]

Then

\[
 A_{1-\rho}(F,G)=-A_\rho(F,G).                               \tag{4}
\]

The complete Xi divisor is reflection-stable with multiplicity.  Nuclear summability permits
reindexing, so `(4)` gives

\[
 \sum_\rho m_\rho A_\rho(F,G)=0.                            \tag{5}
\]

Every fixed point contributes zero already in `(3)`.  Thus the full Meyer character annihilates
the antisymmetrized integrand whose oriented half-sum is Paugam's nondegenerate pairing.  The
cutoff corrections `(2)` cannot be assembled into the retired `Omega_Meyer/Paugam`: on the
relevant wedge their full trace is identically zero.

If the two spectral halves are interchanged, `(1)` changes sign.  Therefore an orientation-free
scalar lift would satisfy \(\psi=-\psi\), hence \(\psi=0\) over \(\mathbb C\), contradicting
Paugam nondegeneracy.  This is an orientation obstruction, not a missing homological calculation.

## Strongest positive survivor

The additive strict comparison

\[
 \Phi:\mathcal E^\bullet_{\mathrm{arith}}
 \longrightarrow C^\bullet_{\mathrm{PZ}},
 \qquad H^1(\Phi):H^1_{\mathrm{arith}}\simeq M_\zeta,
\]

remains valid.  Required refinement has the opposite dependency order:

1. construct global closed arithmetic Calderón relation through every Tate--Milnor,
   residue/corestriction, prime-cusp, and real-orientation attachment;
2. obtain its Hodge-symmetric almost-involution (S), with (S^2-1) nuclear;
3. prove source Green energy has radical exactly closed middle boundaries and hence
   \(\ker S=0\);
4. form canonical polar sign (C=S|S|^{-1}) and Hardy projectors
   \(\Pi_\pm=(1\pm C)/2\);
5. only then define scalar oriented trace
   \[
     \Omega_C(F,G)=
     \operatorname{Tr}\!\left(
       \Pi_+\lambda(F*JG-G*JF)
     \right)                                                  \tag{6}
   \]
   and prove that discrete spectral comparison carries `(6)` to Paugam's `(1)`.

Before step 4, strongest correctly typed comparison target is an orientation-twisted Real relative
trace class attached to the closed Calderón relation, not a scalar cochain cocycle.  Constructing such a
class can be useful, but it does not scalarize Paugam's pairing by itself.

Consequently Route L's first open object is again the global source Hodge object in
`DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`, specifically its closed incidence
Calderón relation and Hodge-symmetric nuclear almost-involution.  Energy-radical and
chirality-kernel theorems are part of producing exact orientation, not downstream decoration.

## Formal status

No new Lean theorem is needed for the algebra behind `(5)`: corpus already formalizes real-valued
involution-odd summation as `HTGeometry.AbstractSpectralFamily.tsum_eq_zero_of_inv_odd` in
`GaloisForLFunctions.HTGeometry.AbstractSpectralCharge`; complex equality follows componentwise.
A divisor-indexed specialization would be target-fed and would not construct source orientation.
Exact Hardy-projector algebra and the
polar-sign lift are already formalized in
`DeningerArithmeticExactHardyProjectors`, `DeningerPolarSignLift`, and
`DeningerPolarSignCFC`.

Formalizing another abstract odd-sum lemma would be rediscovery.  Unformalized scientific content
is arithmetic construction of (S), its kernel theorem on actual relevant coefficient, and
comparison of resulting oriented trace `(6)` with Paugam.

## Falsifier

Exhibit in Meyer or Paugam a scalar degreewise cocycle on raw
(C^\bullet_{\mathrm{PZ}}), defined without an oriented spectral/Hardy half, whose middle
cohomology value is `(1)` and which is not killed by `(5)`.  Primary formulas provide no such
object.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  arXiv:math/0412277.
- Fr\'ed\'eric Paugam, *Spectral symmetries of zeta functions*, arXiv:0803.0199.
- `DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION`.
- `DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR`.
- `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`.
- `DAC_GLOBAL_GREEN_ENERGY_RADICAL`.

## Log

- 2026-08-08 — Retired scalar pre-sector chain transgression after primary-source audit.  Proved
  exact full-character cancellation `(3)`--`(5)` and extracted oriented Calderón survivor `(6)`.
