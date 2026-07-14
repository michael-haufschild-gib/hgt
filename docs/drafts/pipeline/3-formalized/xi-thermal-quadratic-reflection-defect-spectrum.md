# Xi thermal quadratic reflection-defect spectrum

Status: `[PROVED] [FORMALIZED] [NOVELTY UNVERIFIED]`

## Theorem

Let
\[
\lambda_q=(\operatorname{xiSpectralPoint}(q))^{-2},
\qquad x_q=\Re\lambda_q,
\]
with the multiplicity-exact Xi divisor index. Then every thermal node is unconditionally strictly
positive:
\[
x_q>0.
\]
Consequently, the finite positive atomic moments
\[
\widetilde m_{N,n}=\sum_{j<N}x_{q_j}^{n+1}
\]
are finite KMS/Wightman moment sequences without assuming RH, and converge coordinatewise to
\[
\widetilde m_n=\sum_q x_q^{n+1}.
\]

At the quadratic coordinate, if
\[
m_1=\Re\sum_q\lambda_q^2
\]
is the continued prime--Gamma source moment, then
\[
\mathfrak D_2:=\widetilde m_1-m_1
=\sum_q(\Im\lambda_q)^2\ge0.
\]
The reciprocal-square reflection energy satisfies
\[
\sum_q|\lambda_q-\overline{\lambda_q}|^2=4\mathfrak D_2.
\]
The Hermitian square mass
\[
H_2=\sum_q|\lambda_q|^2
\]
satisfies the exact operator-state identities
\[
H_2-m_1=2\mathfrak D_2,
\qquad
\widetilde m_1=\frac{H_2+m_1}{2}.
\]
Hence (m_1\le H_2) unconditionally, and equality—or just the reverse inequality
(H_2\le m_1)—is equivalent to RH.
If (K) denotes the concrete reciprocal Xi diagonal kernel, these two values are themselves
operator invariants:
\[
H_2=\lVert K^2\rVert_{\mathrm{HS}}^2,
\qquad
m_1=\Re\operatorname{Tr}(K^4).
\]
Thus
\[
\lVert K^2\rVert_{\mathrm{HS}}^2-\Re\operatorname{Tr}(K^4)
=2\mathfrak D_2
=\frac12\lVert K^2-(K^2)^*\rVert_{\mathrm{HS}}^2,
\]
the trace-to-norm inequality is unconditional, and its reverse is equivalent to RH.
Finally,
\[
\mathrm{RH}
\iff \mathfrak D_2=0
\iff \widetilde m_1=m_1
\iff \widetilde m_{N,1}\longrightarrow m_1.
\]
Thus the whole thermodynamic moment tower is unnecessary for the RH endpoint: one quadratic KMS
moment is sufficient.

## Projective master zero fibre

The projective reflection radius, the reciprocal-square reflection energy, the quadratic
thermal/source defect, the one-coordinate thermodynamic source limit, and RH have one common zero
fibre. This turns the earlier scale-resolved projective source--temperature spectrum and the finite
KMS construction into a single master law rather than parallel criteria.

More precisely, for every admissible fixed window, the following are one critical datum:

- critical prime--Gamma negative-source abscissa;
- zero projective and Born reflection radii;
- zero endpoint and reciprocal-square reflection energies;
- saturation of the Hermitian-square-mass bound by the prime--Gamma trace value;
- saturation of the intrinsic fourth-trace/Hilbert--Schmidt inequality for the reciprocal kernel;
- equality of the thermal second moment with the continued source moment;
- the reverse thermal/source inequality;
- convergence of the finite KMS second moments to the source value;
- RH.

The theorem simultaneously records the unconditional baseline: every finite truncation is a
KMS/Wightman moment sequence, its second moment converges to the canonical positive thermal value,
and the source moment is bounded above by that value.

The theta source is also an exact countable sum of pure half-line Witten ground-state densities.
Writing its quadratic position-moment functional as `Q_W`, one has

\[
m_1=Q_W>0,
\qquad
\widetilde m_1-\mathfrak D_2=Q_W.
\]

The completed endpoint constant selects the exact transverse factor

\[
\kappa(C)=\frac{16C(1-C)}{(4-5C)^2}<\frac1{20}.
\]

Consequently,

\[
\mathfrak D_2<\frac1{20}\widetilde m_1,
\qquad
\frac{19}{20}\widetilde m_1<Q_W\le\widetilde m_1
<\frac{20}{19}Q_W.
\]

This is strict unconditional progress on the missing estimate, not only a new equivalent form of
the endpoint.

Away from the zero fibre, for every \(0\le\alpha\le\tfrac12\), the same theorem identifies the
source abscissa bound \(1+\alpha\), projective-radius bound, Born-temperature bound, and Xi
half-plane bound. It transports them into the sharp endpoint budget
\[
E\le
\frac{4\alpha^2C}{C^{-1}-3/4-\alpha^2},
\]
and also gives the intrinsic bound obtained by substituting the exact projective radius.

## Positive RH obligation

Every successful construction through this criterion must force the exact source equality
\[
\boxed{\widetilde m_1=m_1.}
\]
Equivalently, it must prove that the canonical unconditional positive KMS second moment equals the
continued prime--Gamma second moment. The finite KMS carrier, its positivity, its convergence, and
the nonnegative discrepancy formula are unconditional; the equality itself remains the unique
RH-bearing estimate. In completely internal operator form, the same obligation is
\[
\boxed{\lVert K^2\rVert_{\mathrm{HS}}^2\le\Re\operatorname{Tr}(K^4)}.
\]

## Formal artifact

Primary module:
`formal/GaloisForLFunctions/RHTower/XiThermalQuadraticReflectionDefectSpectrum.lean`.

Principal declarations:

- `xiThermalNode_pos`
- `finiteKMSWightmanMomentSequence_xiThermalTruncation`
- `tendsto_xiThermalTruncation_one`
- `xiThermalSecondMoment_sub_orientationEnergy_eq_source`
- `xiReciprocalSquareHermitianMass_sub_source_eq_two_orientationEnergy`
- `xiReciprocalSquareHermitianMass_le_source_iff_rh`
- `normalizedPrimeArchMoment_one_eq_re_trace_xiReciprocalKernel_four`
- `xiReciprocalKernel_hsNormSq_sub_reTrace_four_eq_two_orientationEnergy`
- `xiReciprocalKernel_hsNormSq_eq_reTrace_four_iff_rh`
- `xiReciprocalKernel_hsNormSq_le_reTrace_four_iff_rh`
- `xiReciprocalSquareKernel_adjointDefect_hsNormSq_eq_reflectionEnergy`
- `xiReciprocalKernel_normTraceGap_eq_half_adjointDefect`
- `xiThermalSecondMoment_le_source_iff_rh`
- `xiThermalRelativeOrientationFactor_lt_one_twentieth`
- `xiThermalOrientationEnergy_lt_one_twentieth_secondMoment`
- `xiThermalSecondMoment_lt_twenty_over_nineteen_bornWittenSource`
- `xiThermalSquareReflectionDefectEnergy_eq_four_mul_orientationEnergy`
- `xiProjectiveThermalSourceMasterSpectrum`

No theorem in this card assumes RH except in the reverse directions of the displayed equivalences.
