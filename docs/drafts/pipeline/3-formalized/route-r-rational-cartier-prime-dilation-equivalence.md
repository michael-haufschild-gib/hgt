# Route R rational Cartier prime-dilation equivalence

- **ID:** `route-r-rational-cartier-prime-dilation-equivalence`
- **Stage:** 3 — formalized in Lean 4
- **Type:** CLASSICAL ORBIT-RIGIDITY CONSUMER / EXACT RH-EQUIVALENT INTERFACE
- **Status:** `[FORMALIZED] [UNCONDITIONAL] [NO SOURCE PRODUCER] [NOT RH]`
- **Source card:** `../1-in-progress/route-r-rational-cartier-prime-dilation-landing.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RouteRRationalCartierPrimeDilationLanding.lean`

## Formal statement

A `RationalCartierDilationPresentation q gain coefficient` is a polynomial presentation
`H=A/B` with:

- `B != 0` and `B(1) != 0`;
- `A(1)=coefficient*B(1)`;
- `A(qz)B(z)=gain*A(z)B(qz)`.

The formal development proves:

1. coefficient non-erasure makes `H` nonzero as a rational function;
2. the cross-multiplied equation is exactly `H(qz)=gain*H(z)`;
3. comparing leading coefficients forces
   `gain*q^(deg B)=q^(deg A)`;
4. for the actual prime/Xi gain, the centered rate is an integer;
5. the unconditional open Xi strip forces that integer to be zero;
6. the specialized rational landing is equivalent to:
   - the explicit Hodge-mate coefficient being zero;
   - critical-line placement;
   - mate gain one;
   - the fixed same-fibre norm identity;
   - the source-dagger identity;
7. at any fixed ordinary prime, universal landing over Xi support is equivalent to RH.

The leading Xi coefficient's exact reflection parity and equivalence of specialized existence in
the two Gamma orientations are also formalized.

## Scientific status

Orbit rigidity is classical and not new scientific knowledge.  Formal value is exact placement of
the missing Route-R theorem: a coefficient-faithful nonzero rational Cartier potential under prime
dilation is neither weaker nor stronger than the current physical endpoint after specialization.
It is an equivalent and now mechanically searchable interface.

No inhabitant of
`CCMRationalAdelicPrimeXiRationalCartierLanding p rho` is constructed from source data.  The reverse
implication uses the constant potential after assuming the Hodge-mate coefficient is zero and is
present only to prove sharpness of the interface.

## Open producer

Construct the polynomial presentation functorially from pre-divisor
Euler--Gamma--rational-adelic data, retaining the actual multiplicity-leading Xi coefficient and
commuting with both Gamma orientations.  Rationality in the dilation coordinate may not be inferred
from the phrase `rational-adelic` and may not use any RH-equivalent premise.

## Verification

- direct `lake env lean` compile: passed;
- targeted module build: passed;
- axiom report: only `propext`, `Classical.choice`, and `Quot.sound`;
- formal lint: passed;
- umbrella import: wired.
