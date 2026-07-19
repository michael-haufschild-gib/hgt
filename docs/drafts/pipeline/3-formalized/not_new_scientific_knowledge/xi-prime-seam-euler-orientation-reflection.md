# Xi prime-seam Euler orientation reflection

- **ID:** `xi-prime-seam-euler-orientation-reflection`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[VALUE REFLECTION]`, `[OPERATOR INTERFACE]`, `[NOT AN RH PROOF]`
- **Scientific status:** `[PROVED ON PAPER] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `semilocal-projection-phase-polarization.md`

## Goal

Connect three exact structures which are already present but not yet joined in Lean:

1. the FE--Schwarz prime-seam value
   \[
   c_x(\rho)=\log x\left(x^{-\bar\rho}-x^{-(1-\rho)}\right);
   \]
2. the finite Sonin--Euler orientation operator
   \[
   G(u)=\sum_{i,j}(u_i-u_j)C_i^*C_j;
   \]
3. the compressed-source commutator
   \[
   T(u)=[P A(u)P,P A(1)P],\qquad G(u)=-T(u).
   \]

The existing corpus proves the scale-two scalar reflection law, complex real--imaginary
polarization, the boundary factorization of `G`, and the source identity `G=-T`.  It does not
state the general coefficient law, the adjoint law, or their lift to every finite prime packet.

## Exact theorem

Let
\[
R\rho=1-\bar\rho,
\]
the centered FE--Schwarz reflection.  For every real scale `x`, every complex `rho`, and every
finite coefficient packet `u`, the following unconditional identities hold.

### Scalar value reflection

\[
c_x(R\rho)=-c_x(\rho).
\]

At integer and prime scales this strictly generalizes the already formalized scale-two law
`orbitwiseFirstPrimeSeamCharge_lineReflect`.

For every positive integer scale,

\[
c_p(\bar\rho)=\overline{c_p(\rho)},\qquad
c_p(1-\rho)=-\overline{c_p(\rho)}.
\]

The second identity follows by combining the first with centered oddness.

### General finite-orientation law

For `alpha,beta : C` and coefficient packets `u,v`,

\[
G(\alpha u+\beta v)=\alpha G(u)+\beta G(v).
\]

This single complex-linear law subsumes the existing real--imaginary decomposition and supplies
the negation interfaces used by reflection.  Moreover,

\[
G(u)^*=-G(\bar u).
\]

Consequently, real packets give skew-adjoint orientation operators and purely imaginary packets
give self-adjoint orientation operators.  These conclusions require no separately supplied
self-adjointness proposition.

### Canonical finite prime packet

For a finite prime packet `p`, define

\[
G_p(\rho)=G\bigl((c_{p_i}(\rho))_i\bigr),\qquad
T_p(\rho)=T\bigl((c_{p_i}(\rho))_i\bigr).
\]

Then the four FE--Schwarz images obey the exact operator reflection table

\[
\begin{aligned}
G_p(\bar\rho)&=-G_p(\rho)^*, &
G_p(1-\rho)&=G_p(\rho)^*,\\
G_p(1-\bar\rho)&=-G_p(\rho), &
G_p(\rho)&=G_p(\rho).
\end{aligned}
\]

The same table holds for `T_p`, because `G_p=-T_p`.  In particular centered reflection preserves
compactness and essential norm exactly; it does not improve them.

## Paper proof

Centered scalar oddness is direct substitution:

\[
\overline{1-\bar\rho}=1-\rho,
\qquad
1-(1-\bar\rho)=\bar\rho,
\]

so the two powers in `c_x` exchange places.  For a positive real base, complex conjugation
commutes with its complex power; this gives `c_p(\bar\rho)=\overline{c_p(\rho)}`.  Applying
centered oddness to `\bar\rho` gives the functional-equation identity.

Complex linearity of `G` follows from

\[
(\alpha u_i+\beta v_i)-(\alpha u_j+\beta v_j)
=\alpha(u_i-u_j)+\beta(v_i-v_j).
\]

For the adjoint law, reverse the two ordered indices:

\[
\begin{aligned}
G(u)^*
 &=\sum_{i,j}\overline{u_i-u_j}\,C_j^*C_i\\
 &=\sum_{i,j}\overline{u_j-u_i}\,C_i^*C_j\\
 &=-G(\bar u).
\end{aligned}
\]

Substitution of the three scalar reflection identities yields the operator table.  Finally,
adjoint and multiplication by `-1` preserve the compact ideal and the Calkin norm, so every
reflection image has exactly the same compactness obstruction.

## Hostile audit and no-go closure

- The actual prime Euler corner is noncompact; Hilbert--Schmidt or trace-class Ward energy is the
  wrong quotient for this source.
- The reflection table is equivariance, not coercivity.  It transports a nonzero Calkin class to
  another member of the Xi quartet and cannot make that class vanish.
- At a critical-line fixed point, centered oddness forces the scalar seam and the orientation
  operator to vanish.  The missing assertion that every Xi divisor point is fixed is RH itself,
  so this observation is not a proof mechanism.
- No standalone scientific novelty is claimed.  The positive survivor is the exact all-scale,
  all-finite-packet reflection classification and the discharge of adjoint/Prop interfaces.

## Relation to the literature

Burnol's Sonine/co-Poisson work supplies the Fourier/Sonine setting, while Connes--Consani's
semilocal operator programme and quasi-inner local-factor analysis explain why compact off-diagonal
operators and the Calkin quotient are the natural source language.  The exact finite-packet
reflection table above was not located as a named result in that literature; its ingredients are
standard involutive operator algebra plus the corpus's canonical seam coefficient.

Primary sources:

- J.-F. Burnol, *On Fourier and zeta(s)*, https://arxiv.org/abs/math/9902080
- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, https://arxiv.org/abs/math/0105120
- A. Connes and C. Consani, *The Scaling Hamiltonian*, https://arxiv.org/abs/1910.14368
- A. Connes and C. Consani, *Quasi-inner functions and local factors*,
  https://arxiv.org/abs/2008.10974

## Formalization gates

- [x] live corpus and failed-route audit
- [x] primary-source novelty audit
- [x] hostile mathematical audit
- [x] dependency-closed paper proof
- [x] general finite-orientation complex-linearity law
- [x] finite-orientation adjoint law
- [x] real skew-adjoint and imaginary self-adjoint Prop interfaces
- [x] all-scale centered seam reflection
- [x] positive-integer Schwarz and FE seam reflections
- [x] finite prime-packet operator reflection table
- [x] source-commutator reflection table
- [x] compactness and essential-norm reflection interfaces
- [x] exact Lean build and axiom audit
- [x] promotion to Stage 3

## Lean certificate

Modules:

- `formal/GaloisForLFunctions/RHTower/SoninCalkinNormBound.lean`
- `formal/GaloisForLFunctions/RHTower/SemilocalEulerPhasePolarization.lean`
- `formal/GaloisForLFunctions/RHTower/XiPrimeSeamCoherenceCollapse.lean`
- `formal/GaloisForLFunctions/RHTower/XiPrimeSeamEulerOrientationReflection.lean`

The adjoint-compactness theorem was moved from the much larger finite-word Sonin module into the
essential-norm layer, so the new reflection module does not widen its dependency cone merely to
obtain adjoint invariance.

Main declarations:

- `finiteEulerOrientationMatrix_linearCombination`
- `finiteArchimedeanEulerOrientationGram_linearCombination`
- `adjoint_finiteArchimedeanEulerOrientationGram`
- `adjoint_finiteArchimedeanEulerOrientationGram_ofReal`
- `finiteArchimedeanEulerOrientationGram_ofImag_isSelfAdjoint`
- `orbitwiseScaleSeamCharge_lineReflect`
- `orbitwiseScaleSeamCharge_conj`
- `orbitwiseScaleSeamCharge_one_sub`
- `isCompactOperator_adjoint_iff`
- `essentialNorm_adjoint`
- `orbitwiseFinitePrimeEulerOrientationGram_lineReflect`
- `adjoint_orbitwiseFinitePrimeEulerOrientationGram`
- `orbitwiseFinitePrimeEulerOrientationGram_one_sub`
- `orbitwiseFinitePrimeEulerCompressionCommutator_lineReflect`
- `adjoint_orbitwiseFinitePrimeEulerCompressionCommutator`
- `orbitwiseFinitePrimeEulerCompressionCommutator_one_sub`
- the corresponding compactness and essential-norm reflection interfaces

Validation:

- exact module builds passed; no full project build was run;
- the scoped proof-debt scan is empty;
- representative `#print axioms` checks report only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Remaining RH core

`[OPEN CORE]` Construct the completed prime--Gamma source action on the actual Sonin carrier and
prove the source-side compactness/coercive sign which kills the finite Calkin orientation class on
every Xi divisor fibre.  Reflection equivariance alone preserves that class and cannot discharge
this gate.
