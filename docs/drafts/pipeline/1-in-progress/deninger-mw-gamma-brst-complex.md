# Deninger Milnor--Witt--Gamma BRST complex

- **ID:** `deninger-mw-gamma-brst-complex`
- **Stage:** 1-in-progress
- **Type:** CONJECTURAL CONSTRUCTION
- **Parent:** `deninger-milnor-witt-hodge-realization`
- **Lean consumers:** `HTGeometry.BRSTHodgeConstraint`,
  `DeningerArithmeticRectangularQuaternionicHodge`,
  `DeningerArithmeticSourceGreen`

## Exact purpose

Construct the missing coefficient complex \(R\alpha_*\mathscr G\) on Deninger's rational-Witt
flow space from quantized arithmetic incidence.  Milnor--Witt/\(\mathrm{ko}\) supplies the
Steinberg boundary and indefinite Poincare transfer; Gamma and rectangular prime atoms supply a
fixed positive chain metric.  Harmonic cohomology, not the bare transfer form, supplies the
positive Hodge realization.

## Prior-route constraints

1. A generic conservative colligation is only an RH criterion unless its metric and comparison
   vector are fixed before continuation.
2. The orbit-diagonal Gamma--Sonin lift has positive odd kernel
   \[
     K^-_\Gamma(h,k)
       =(\cosh(h-k))^{-1/2}-(\cosh(h+k))^{-1/2},
   \]
   but erases the Mobius sign and has the wrong critical energy.  Incidence must be applied before
   Gamma completion.
3. Bare Milnor--Witt degree \(p_\epsilon\) is indefinite over \(\mathbb R\).  It supplies a
   transfer pairing, not a Hilbert norm.
4. Scalar analytic gauges and divisor-faithful moment metrics either lose source incidence or
   restate RH.  A valid source object needs a pre-divisor quantized charge.  Milnor--Witt
   Steinberg boundaries and hermitian \(K\)-classes provide exactly such candidate charges.
5. Real Betti realization of very effective hermitian \(K\)-theory is connective
   \(L(\mathbb R)\), so ordinary Betti realization still records an indefinite signature theory.
   Gamma polarization is additional arithmetic boundary data.

## Finite-stage construction

For a finite prime set \(S\), a power bound \(N\), and an archimedean cutoff \(A\), define a
three-term finite Hilbert cochain complex
\[
 C^\bullet_{S,N,A}
   =\left(C^0_{S,N,A}\xrightarrow{Q^0_{S,N,A}}
          C^1_{S,N,A}\xrightarrow{Q^1_{S,N,A}}
          C^2_{S,N,A}\right).                                      \tag{1}
\]

The incidence differential is now fixed, rather than conjectural.  Let \(M_S\) be the free
multiplicative monoid on \(S\), acting on a finite Milnor--Witt--Gamma coefficient packet
\(V_{S,N,A}\) through the framed power transfers \(T_n\).  Use the inhomogeneous bar
coboundaries
\[
\begin{aligned}
 (Q^0v)(n)&=T_nv-v,\\
 (Q^1\phi)(m,n)&=T_m\phi(n)-\phi(mn)+\phi(m),\\
 (Q^2\psi)(\ell,m,n)
   &=T_\ell\psi(m,n)-\psi(\ell m,n)+\psi(\ell,mn)-\psi(\ell,m).
\end{aligned}                                                       \tag{2}
\]
Then set
\[
 C^0=V_{S,N,A},\qquad
 C^1=\operatorname{Map}_{S,N}(M_S,V_{S,N,A}),\qquad
 C^2=\ker Q^2.                                                       \tag{3}
\]
The subscript \(S,N\) means non-unit tuples whose total valuation weight
\(\sum_{i,p\in S}v_p(n_i)\) is at most \(N\).  This cutoff is stable under every bar face,
unlike the unstable size cutoff \(n\le N\).  The good truncation \(C^2=\ker Q^2\) retains the
actual degree-two cocycle condition.

The paper proof and abstract Lean formulation in `deninger-power-bar-cochain` give
\[
 Q^1Q^0=0,\qquad Q^2Q^1=0.
\]
Thus `(1)` is a genuine cochain complex as soon as \(T_mT_n=T_{mn}\).  The determinant-level
orientation compatibility for the monic presentations is proved in
`deninger-power-map-orientation-coherence`; the remaining higher framing-path coherence must
still be supplied by the framed-correspondence infinity-category.  Milnor--Witt Steinberg
relations live in \(V_{S,N,A}\) and its cup product, not as an ad hoc replacement for the bar
identity.

The positive chain metric is fixed before taking cohomology:

1. endpoint Tate generators have their standard positive norm;
2. each prime tube uses the rectangular energy
   \[
     \|(z,w)\|_{p,r}^2=|z|^2/r+r|w|^2;
   \]
3. archimedean odd incidence uses \(K^-_\Gamma\);
4. different finite generators are paired only by the source incidence laws, never by Xi-zero
   evaluation.

Let \(Q_{S,N,A}\) be the total odd differential on the Hilbert direct sum of `(1)`.  Define
\[
 \Delta_{S,N,A}=Q_{S,N,A}^\dagger Q_{S,N,A}
                 +Q_{S,N,A}Q_{S,N,A}^\dagger.                      \tag{4}
\]
Finite-dimensional Hodge theory then gives
\[
 \ker\Delta_{S,N,A}
   =\ker Q_{S,N,A}\cap\ker Q_{S,N,A}^\dagger
   \cong H^\bullet(C^\bullet_{S,N,A}),                              \tag{5}
\]
with a positive metric inherited from the chain space.  Equations `(4)`--`(5)` are already
formalized abstractly in `HTGeometry.BRSTHodgeConstraint`; source work is construction of
\(Q_{S,N,A}\) and its fixed metric.

## Flow and odd Hodge

Framed power maps first define pullback \(V_n\) and pushforward \(F_n\).  The
projection formula makes them Poincare adjoints and motivic degree gives
\(F_nV_n=n_\epsilon\).  The exact Gamma specialization is now isolated as
\[
 \operatorname{Real}^{\mathrm{pol}}_\Gamma(n_\epsilon)=n\,\mathrm{id}.
\]
`deninger-gamma-rank-character-rigidity` proves that this scalar law is forced, rather than an
independent choice: any unital real \(GW\)-character strictly positive on the hyperbolic plane
must be rank, hence sends every \(n_\epsilon\) to \(n\).  What remains is to construct the
Gamma realization, prove that its hyperbolic scalar channel is strictly positive, and prove that
the motivic push--pull degree acts through that channel.

`deninger-hyperbolic-localization-rank-collapse` strengthens this from uniqueness to an algebraic
construction.  Base change along
\[
 GW\longrightarrow GW[h^{-1}],\qquad h=1+\epsilon,
\]
forces \(\epsilon=1\) because \((1-\epsilon)h=0\), and therefore forces
\(n_\epsilon=n\) before any Hilbert completion.  Over a real closed field the localized
coefficient algebra is the rank summand \(\mathbb Z[1/2]\); the signature summand is annihilated.
This is the algebraic Gamma rank boundary.  Remaining analytic task is its functorial positive
odd Hilbert realization and compatibility with the MW incidence complex.

Together with moving-Hodge naturality, `deninger-polarized-transfer-half-density` proves that
\[
 U_n=n^{-1/2}V_n
\]
is an isometric multiplicative semigroup.  Its unnormalized generator has the forced weight-one
decomposition \(V_n=e^{(\log n)/2}U_n\).

The finite-stage centered flow \(\Theta_{S,N,A}-\tfrac12\) is the generator of the \(U_n\)
action.  Required identities are
\[
 [\Theta_{S,N,A},Q_{S,N,A}]=0,\qquad
 [\Theta_{S,N,A},\Delta_{S,N,A}]=0.                                \tag{6}
\]
At finite dimension the second identity follows from the first once the \(U_n\)-action is
unitary: commuting a unitary with \(Q\) also commutes it with \(Q^\dagger\), hence with
\(\Delta\).  `deninger-unitary-brst-hodge-descent` proves this implication and harmonic-sector
preservation unconditionally.  The source obligations are therefore the framed transfer action,
positive realization of the localized Gamma rank channel, and moving-Hodge naturality.  No
Xi-zero location is involved in this reduction.

The odd Hodge operator is the phase-polarized supercharge on harmonic degree one, calibrated by
the rectangular formula
\[
 J_r(z,w)=(-rw,z/r),\qquad \star_r=J_r\circ\text{conjugation},
 \qquad\star_r^2=-1.                                                \tag{7}
\]
It is not the real Betti signature involution and not the bare MW transfer.

## Cofinal theorem target

`[CONJECTURE] [DAC_MW_GAMMA_BRST_COFINALITY]`:

There are cofinal choices of \((S,N,A)\) and isometric chain embeddings for which:

1. \(Q_{S,N,A}\) converges on the algebraic union to a closable differential \(Q_\infty\);
2. the Friedrichs closures of \(\Delta_{S,N,A}\) converge in strong resolvent sense to
   \(\Delta_\infty\);
3. harmonic projections converge strongly, with no loss of source classes;
4. reduced harmonic cohomology is concentrated in degrees \(0,1,2\), with
   \(H^0\simeq\mathbb C(0)\), \(H^2\simeq\mathbb C(-1)\);
5. degree-one cup/trace agrees with the prime--Gamma radical quotient pairing;
6. centered Frobenius and the odd Hodge operator commute on harmonic \(H^1\);
7. the resulting Green map into `DeningerArithmeticCompletedCohomology` has dense range and is
   cup-isometric;
8. finite graded traces converge distributionally to the complete prime-power plus
   archimedean Lefschetz distribution;
9. regularized determinant equals completed zeta.

All definitions through clause 6 must precede Xi-divisor comparison.  Clauses 7--9 are
comparison theorems, not construction inputs.

## Falsifiers

- If \(Q\) is diagonal in prime-orbit generators, the construction is rejected by the proved
  Gamma--Sonin sign-erasure/super-four theorem.
- If the chain norm is selected after evaluating \(Q\) or \(\Theta\), the construction is metric
  rescaling theatre.
- If framed MW data are forgotten before the incidence boundary is formed, ordinary
  rational-Witt cohomology retains the Steinberg defect.
- If Gamma rank collapse, moving-Hodge naturality, or `(6)` is proved by identifying harmonic
  classes with Xi zeros and assuming their centered eigenvalues real, RH has been assumed.
- If cofinal harmonic projections lose classes or fail strong convergence, finite Hodge theory
  does not produce the desired reduced cohomology.

## Current boundary

- `[LITERATURE-COVERED]` Integral MW motivic spectrum over \(\mathbb Z\), integral
  \(\mathrm{ko}\), framed-transfer and normed-algebra machinery.
- `[PAPER-CHECKED]` Each power map \(x\mapsto x^n\) has a finite-syntomic framing from the monic
  regular presentation \(x^n-y\).  The induced determinant orientations compose with no sign or
  unit defect; coherent paths in the full algebraic \(K\)-theory framing space remain open.
- `[PROJECT-PROVED]` The exact bar coboundaries \(Q^0,Q^1,Q^2\), their nilpotence, good
  degree-two truncation, and valuation-stable finite filtration.
- `[PROJECT-PROVED]` Strict hyperbolic positivity rigidly forces the Gamma scalar character to be
  rank, and therefore forces \(n_\epsilon\mapsto n\); the abstract polarized-transfer theorem
  then forces the \(n^{1/2}\) half-density law.
- `[PROJECT-PROVED]` Hyperbolic localization constructs the rank coefficient channel
  algebraically and forces \(n_\epsilon=n\) without a positivity assumption.
- `[PROJECT-PROVED]` A unitary centered chain transfer automatically commutes with
  \(Q^\dagger\), \(\Delta\), and the finite harmonic sector; Laplacian equivariance is no longer
  an independent gate.
- `[PROJECT-PROVED]` The hyperbolically localized Gamma-rank boundary has an explicit positive
  odd realization on \(\ell^2(\mathbb Q_{>0}^{\times}\sqcup
  \mathbb Q_{>0}^{\times},\mathbb C)\).  Its algebraic core is dense; centered power shifts are
  unitary cup/Hodge intertwiners; Hodge commutes with \(Q^0,Q^1,Q^2\) and preserves
  \(\ker Q^2\).
- `[PROJECT-PROVED]` Source H0/H1/H2 algebraic complex, source prime--Gamma Poincare pairing,
  rectangular quaternionic atom, BRST--Hodge operator algebra, determinant/Lefschetz consumers.
- `[OPEN CORE]` Construct the MW/\(\mathrm{ko}\) coefficient packet and coherently framed
  transfer action; prove the MW/Steinberg relation subspace is closed and stable under the
  constructed Gamma Hodge operator; prove moving-Hodge naturality; then construct the cofinal
  analytic limit.
- `[NO RH CLAIM]` Clause 6 is still open and is the decisive purity theorem.

## Log

- 2026-07-26 — construction isolated after MW-over-\(\mathbb Z\) literature correction and
  bare-transfer positivity no-go.
- 2026-07-26 — bar differential, determinant orientation, Gamma rank rigidity, and
  polarized-transfer half-density law proved on paper; unconditional Lean interfaces drafted.
