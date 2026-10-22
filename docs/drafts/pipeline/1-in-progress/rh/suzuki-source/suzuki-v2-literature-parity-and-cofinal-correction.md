# Suzuki v2 literature parity and cofinal correction

**Status:** all eleven labeled v2 results formalized in Lean; corrected pole-free cofinal convergence remains open  
**Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
arXiv:2606.09096v2, 17 August 2026.

## Scope and exactness

This card records only source theorem parity and the analytic correction forced by the v2 limit.
The RH route map is read-only.  A declaration about arbitrary matrices or an abstract predicate does
not count as a formalization of a source theorem.

## Labeled-result audit against Lean code

The v2 paper has five theorems, two corollaries, three lemmas, and one proposition.

| Source result | Exact Lean status |
|---|---|
| Theorem 1.1, `A_a` is the Friedrichs extension of `B_a=D^*G_aD` | Closed by the literal form/operator construction in `SuzukiWeilFriedrichsOperator`, the exact graph inclusion in `SuzukiFriedrichsExtension`, and the form-core theorem in `SuzukiDirichletFormCore`. |
| Corollary 1.2, smooth-core Rayleigh infimum and form closure | Closed by `SuzukiRayleighInfimum`. |
| Theorem 1.3, continuity of `a \mapsto \lambda_a` | Closed by `SuzukiGroundEnergyContinuity`. |
| Theorem 1.4, small-aperture positivity, sharp asymptotic, simplicity, evenness | Closed by `SuzukiSmallApertureTheoremOneFour`. |
| Theorem 1.5, deficiency-index extension characteristic is entire, spectral, and real-zeroed | Closed on the actual energy Hilbert space. `SuzukiTaSymmetry` proves source-core symmetry; `SuzukiTaCharacteristicRealization` constructs the literal von Neumann extensions; `SuzukiTaSpectralEigenspace` proves every complex adjoint eigenspace is the canonical Riesz line; `SuzukiTaCharacteristicZeros` proves exact zero/eigenvalue equivalence and reality; `SuzukiTaCharacteristicEntire` proves Suzuki's physical Fourier formula and entireness. |
| Corollary 1.6, v2 compact-open limit to `xi/(xi+xi')` implies RH | Closed by `suzukiV2CharacteristicLimitWall_implies_riemannHypothesis`. The same module proves the literal premise impossible and isolates the corrected pole-free meromorphic survivor. |
| Lemma 3.1, `B_a \subset A_a` | Closed by `suzukiDirichletScrewOperator_le_weilFriedrichsOperator`. |
| Proposition 4.1, compact `H^log(I) \hookrightarrow L^2(I)` | Closed by `SuzukiHlogCompactEmbedding`. |
| Lemma 6.1, symmetry of the actual derivative on `H(T_a)` | Closed by `suzukiTaSmoothCoreIDeriv_symmetric`, using the actual restricted Weil form and physical embedding. |
| Lemma 6.2, deficiency indices `(1,1)` | Closed by `suzukiTaShiftedDerivativePMap_deficiencyIndices`; its proof repairs the norm-continuity gap in the paper by identifying shifted-range closures with explicit moment hyperplanes. |

## Paper proof A: Lemma 6.1 without an adjoint-domain shortcut

Fix `a>0` and the canonical real `lambda` strictly below the localized Weil-form floor.  Let
`T_a=A_a-lambda` and let `D=i d/dx` on the literal core `C_c^infty(-a,a)`.  For core vectors `u,v`,

`<Du,v>_T = Q_W^a(Du,v)-lambda <Du,v>_2`.

The `L^2` term is symmetric by compact-support integration by parts.  For the Weil term, use its
literal Hermitian-correlation realization

`Q_W^a(u,v)=W(v * tilde u)`.

The Fourier transform of `D u=i u'` is the real multiplier `-2 pi xi` times the Fourier transform
of `u`.  Hence, pointwise in frequency,

`overline(F(Du)) F(v) = overline(F(u)) F(Dv)`.

Fourier injectivity on Schwartz space gives

`v * tilde(Du) = (Dv) * tilde u`.

Applying the same literal Weil distribution proves `Q_W^a(Du,v)=Q_W^a(u,Dv)`.  Therefore
`<Du,v>_T=<u,Dv>_T`.  This proves symmetry directly on the actual source core, without the invalid
implication “continuous in the stronger form norm, hence continuous in the weaker L2 norm”.

## Paper proof B: Theorem 1.5

Let `S` be the symmetric operator from Paper proof A.  The already-proved exact shifted-range
closure law gives

`dim ker(S^*-i)=dim ker(S^*+i)=1`.

Choose nonzero vectors `v_+` and `v_-` in these deficiency spaces and rescale them to equal norm.
For `q=exp(i theta)`, von Neumann's extension theorem applied to the unitary map
`v_+ \mapsto q v_-` gives a self-adjoint extension `S_theta`.  Its domain is equivalently the
maximal isotropic boundary hyperplane

`{v in D(S^*) : B(v,v_+ + q v_-)=0}`,

where `B(x,y)=<S^*x,y>_T-<x,S^*y>_T`.

For every `z in C`, compact support makes

`u \mapsto integral u(x) exp(i conjugate(z) x) dx`

a continuous linear functional on `H(T_a)`.  Let `v_z` be its Riesz vector.  Compact-support
integration by parts yields `S^*v_z=z v_z`; the functional is nonzero, and the one-dimensional
adjoint eigenspace is therefore spanned by `v_z`.

Expanding `B(v_z,v_+ + qv_-)=0` and using the Riesz identities gives exactly Suzuki's function

`W(a,theta;z)=(z-i) integral v_+(x) exp(i z x) dx
              +q(z+i) integral v_-(x) exp(i z x) dx`,

up to one globally nonzero normalization caused only by the conjugate-first Lean inner-product
convention.  Each integral is the entire Fourier transform of compactly supported `L^2` data, so
`W` is entire.  The boundary equation is equivalent to `v_z in D(S_theta)`, hence

`W(a,theta;z)=0  iff  z is an eigenvalue of S_theta`.

Self-adjointness forces every such `z` to be real.  Conversely every eigenvector of `S_theta` is an
adjoint eigenvector and therefore lies on the one-dimensional line spanned by `v_z`; its boundary
condition forces `W=0`.  This proves every clause of Theorem 1.5.

## Paper proof C: literal v2 Corollary 1.6

In centered notation `XiC(z)=xi(1/2+i z)`, evenness and the chain rule give

`xi(1/2-i z)=XiC(z)`,

`xi'(1/2-i z)=i XiC'(z)`.

Thus the v2 target is

`T_v2(z)=XiC(z)/(XiC(z)+i XiC'(z))`.

On any preconnected open pole-free domain containing the centered Xi divisor, locally uniform
convergence of the entire real-zero characteristics to `T_v2` transfers every zero of `XiC` to the
closed real axis by Hurwitz.  Therefore the corrected meromorphic version of the convergence
premise implies RH.  The literal all-of-`C` compact-open premise is stronger; if coherent, it has
the same consequence.

## New theorem: the literal v2 compact-open convergence is impossible

Define on the positive real ray

`L(c)=Re(xi'/xi(1/2+c))`.

The corpus proves `L(0)=0`, continuity of `L`, and

`L(c)/log c -> 1/2` as `c -> +infinity`.

Consequently `L(c)->+infinity`.  The intermediate value theorem supplies `c>0` with `L(c)=1`.
Put `z_c=-ic`.  The completed Xi function is nonzero there because
`XiC(-ic)=xi(1/2+c)` lies on the zero-free positive real Xi ray.  Schwarz reality makes the real
logarithmic derivative equal to `1`, and the centered chain rule gives

`XiC'(z_c)=i XiC(z_c)`.

Therefore

`XiC(z_c)+i XiC'(z_c)=0`, while `XiC(z_c) != 0`.

So `T_v2` has a genuine pole at `z_c`.  A locally uniform limit on all of `C` of entire functions
is entire, hence no family `exp(phi(a,z)) W(a,theta(a);z)` with holomorphic finite gauges can
converge uniformly on every compact subset of `C` to the displayed v2 target.

This is not RH: it is an unconditional correction of the two-day-old conjectural convergence
statement.  The surviving cofinal problem is necessarily meromorphic convergence on pole-free
domains (or spherical convergence), together with source-faithful boundary transport.  That
survivor remains RH-bearing.

## Lean realization and verification

The new dependency-closed realization consists of:

- `HTGeometry/VonNeumannDeficiency.lean`: closure/adjoint decomposition, boundary pairing,
  one-dimensional unitary extension, and self-adjointness.
- `RHTower/SuzukiTaSymmetry.lean`: actual `H(T_a)` derivative symmetry (Lemma 6.1).
- `RHTower/SuzukiTaCharacteristicRealization.lean`: normalized actual deficiency vectors,
  boundary family, self-adjoint extensions, and canonical spectral Riesz vectors.
- `RHTower/SuzukiTaSpectralEigenspace.lean`: exact complex shifted-range closure and
  one-dimensional adjoint eigenspaces for every spectral parameter.
- `RHTower/SuzukiTaCharacteristicZeros.lean`: exact characteristic-zero/eigenvalue equivalence
  and real-zero theorem.
- `RHTower/SuzukiTaCharacteristicEntire.lean`: literal physical Fourier formula and entireness.
- `RHTower/SuzukiV2CharacteristicTarget.lean`: exact v2 target, conditional Corollary 1.6,
  unconditional pole obstruction, and corrected meromorphic implication.
- `RHTower/SuzukiV2SphericalConvergence.lean`: exact pole-free finite-chart convergence and the
  two-chart spherical formulation, including compactwise eventual zero-freeness in the reciprocal
  chart; spherical convergence formally implies the corrected meromorphic wall and RH.

All eight modules pass direct `lake env lean` checks.  Fresh targeted `.olean` builds pass for the
dependency roots and capstones; both theorem-area umbrellas import the new modules without an
umbrella build.  Representative `#print axioms` checks report only `propext`, `Classical.choice`,
and `Quot.sound`.  No declaration in these modules contains `sorry`, `admit`, a project `axiom`,
`opaque`, or `unsafe`.

## Heavy-conjecture loop

1. **C1 — literal entire compact-open convergence on all `C`: falsified.**  The unconditional
   negative-imaginary pole above contradicts Weierstrass closure.
2. **C2 — holomorphic exponential gauges repair C1: falsified.**  Such gauges keep every finite
   approximant entire; their locally uniform limit on `C` is still entire.
3. **C3 — locally uniform convergence on a pole-free domain retaining every Xi zero: survives.**
   It is analytically coherent and still implies RH by local Hurwitz transfer.  Constructing this
   source-locked convergence is the corrected hard frontier.
