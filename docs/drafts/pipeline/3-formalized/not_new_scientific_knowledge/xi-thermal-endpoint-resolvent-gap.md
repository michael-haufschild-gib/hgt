# Xi thermal endpoint-resolvent gap law

- **ID:** `xi-thermal-endpoint-resolvent-gap`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); bounded static-observable reduction; exact RH equality criterion
- **Scientific status:** `[PROVED] [NOT AN RH PROOF] [NOVELTY NOT CLAIMED]`
- **Source:** completed Xi endpoint value and the positive reciprocal-square thermal spectrum

## Main law

For a multiplicity-exact Xi-zero copy `q`, put

\[
 z_q=-\frac{1}{(\rho_q-\tfrac12)^2},
 \qquad x_q=\Re z_q>0.
\]

Define

\[
 C=2+\gamma_E-\log(4\pi),
 \qquad
 T=\sum_q\frac{x_q}{1+x_q/4}.
\]

The pointwise identity

\[
 \Re\frac{z}{1+z/4}-\frac{x}{1+x/4}
 =
 \frac{(\Im z)^2}
 {4(1+x/4)\lvert1+z/4\rvert^2},
 \qquad x=\Re z>0,
\]

is absolutely summable over the complete Xi divisor.  Hence

\[
 C-T=D,
 \qquad
 D:=\sum_q
 \frac{(\Im z_q)^2}
 {4(1+x_q/4)\lvert1+z_q/4\rvert^2}
 \ge0.
\]

Every denominator is strictly positive, so

\[
 D=0
 \iff \Im z_q=0\text{ for every }q
 \iff \mathrm{RH}.
\]

Equivalently,

\[
 0<\frac{T}{C}\le1,
 \qquad
 \frac{T}{C}=1\iff\mathrm{RH},
\]

and failure of RH makes `T/C` a strict contraction.

## Unitary phase-locking form

For each atom set

\[
 u_q=\frac{1+\overline{z_q}/4}{1+z_q/4}.
\]

Accretivity gives `|u_q|=1`, and the same defect has the exact unitary leakage form

\[
 D=\sum_q\frac{|1-u_q|^2}{1+x_q/4}.
\]

Consequently

\[
 \mathrm{RH}
 \iff (\forall q,\ u_q=1)
 \iff T/C=1.
\]

This is the static scattering version of the result: the non-self-adjoint transverse coordinate
is exactly a phase leakage, and RH is complete phase locking.  It identifies an invariant-subspace
or inner-function style obligation that can be attacked without reconstructing the moment tower.

## Quantitative source window

Let

\[
 E=\sum_q(\Im z_q)^2
   =\text{thermal second moment}-\text{prime--Gamma source second moment}.
\]

The resolvent denominator is at least `4` atomwise, so the bounded defect is a contraction of the
quadratic orientation energy:

\[
 0\le D\le \frac{E}{4}.
\]

Combining this with the existing exact cubic endpoint budget gives the source-explicit bound

\[
 0\le C-T=D
 \le \left(\frac{C}{4-C}\right)^3
 <\frac1{600000}.
\]

Thus the unconditional positive observable already lies in the narrow interval

\[
 C-\frac1{600000}<T\le C.
\]

The remaining issue is exact saturation, not control of the size of the discrepancy.

## Finite static-observable form

For the fixed multiplicity-exact enumeration `q_j`, let

\[
 T_N=\sum_{j<N}\frac{x_{q_j}}{1+x_{q_j}/4}.
\]

The finite positive systems converge unconditionally:

\[
 T_N\longrightarrow T.
\]

Therefore the thermodynamic obligation is reduced from convergence of the complete moment tower
to one bounded rational observable:

\[
 T_N\longrightarrow C
 \iff \mathrm{RH}.
\]

If the finite thermal measure is written as

\[
 \mu_N=\sum_{j<N}x_{q_j}\,\delta_{x_{q_j}},
\]

then

\[
 T_N=\int\frac{1}{1+x/4}\,d\mu_N(x).
\]

Thus only the bounded resolvent observable `(I+A/4)^{-1}` must be calibrated in the static
operator-state model; constructing a Hamiltonian flow or proving convergence of every vacuum
moment is unnecessary for this criterion.

## Direct prime-polar consequence

For every admissible rectangular prime-polar tail,

\[
 \sigma_{\rm abs}\!\left(
   \sum_n S^-_{L,N}(n)n^{-s}
 \right)\le1
 \iff T=C
 \iff T_N\longrightarrow C.
\]

This is an exact theorem connection, not a new hypothesis interface.

## Exact open core

The formal corpus now proves `T ≤ C` unconditionally and `T < C` under `¬RH`.  Completing RH is
therefore exactly the reverse source calibration

\[
 C\le T,
\]

or equivalently the bounded finite-system value convergence `T_N → C`.  Functional-equation and
Schwarz reindexing alone preserve `x_q`; they do not evaluate this mixed Hermitian diagonal.  A
closing argument must supply a source identity or a positive operator-state calibration for this
one bounded observable.

## Formal artifact

- `formal/GaloisForLFunctions/RHTower/XiThermalEndpointResolventGap.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`

Principal declarations:

- `re_quarterResolvent_sub_realQuarterResolvent`;
- `xiEndpointCompletedCurvature_sub_thermalEndpointResolventValue_eq_defect`;
- `xiThermalEndpointResolventDefect_eq_zero_iff_rh`;
- `xiThermalEndpointResolventDefect_eq_phaseLockingEnergy`;
- `forall_xiThermalEndpointScatteringPhase_eq_one_iff_rh`;
- `xiThermalEndpointResolventDefect_le_quarter_orientationEnergy`;
- `xiThermalEndpointResolventDefect_le_endpointRadius_cube`;
- `xiThermalEndpointResolventValue_source_window`;
- `tendsto_xiThermalEndpointResolventTruncation`;
- `tendsto_xiThermalEndpointResolventTruncation_endpointCurvature_iff_rh`;
- `xiThermalEndpointResolventContraction_le_one`;
- `xiThermalEndpointResolventContraction_eq_one_iff_rh`;
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_thermalEndpointResolvent_saturation`;
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_tendsto_thermalEndpointResolvent`;
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_endpointPhaseLocking`.

The module has no placeholders.  Axiom inspection of the main law, finite-limit capstone,
contraction criterion, and prime-polar theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`.
