# Completed conductor packets at growing overlap

Write $A_{c,N}$ for the complete tilted-spline Weil matrix, $r_{m,N}$ for its
normalized Ramanujan vector, and $E_m(c)$ for the completed conductor energy.
The exact residual $A_{c,N}r_{m,N}-E_m(c)r_{m,N}$ contains eight terms:
prime adjunction, self remainder, polar center, separated cross remainder,
two-pole remainder, near Gamma/downward cancellation, near center, and upward
shell realization.

The available source bounds, with constants depending on the fixed conductor,
are:

| Squared norm | Bound | Source |
|---|---|---|
| Prime adjunction residual | $C_m/\log N$ | `SignedArithmeticHodgeTheory/OneArithmeticRemainderControlsEveryRamanujanResidual`, `TheArithmeticResidualBudgetIsUniformInTheHorizon` |
| Self remainder | $C_m c^2/N^2$ | `CriticalArithmeticCorrelationTheory/WeilReplacementErrorsHavePolynomialCost` |
| Polar center residual | $C_m c^2/\log N$ | same |
| Separated cross and two-pole remainders | $C_m c^4/\log N$ | same |
| Near Gamma/downward cancellation and near center | $C_m c^5/\log N$ | `NearGammaDownwardCancellationHasPolynomialGrowth` |
| Affine shell residual | $C_m c^6/\sqrt{\log N}$ | `AffineShellErrorsHavePolynomialHarmonicBounds` |
| Prime cutoff replacement at strip width $B$ | $C_m(B+1)^6/\sqrt{\log N}$ | `PrimeBoundaryErrorsHavePolynomialHarmonicBounds` |
| Logarithmic kernel replacement | $C_m c^4(B+1)^6/\sqrt{\log N}$ | `UpwardKernelLinearizationHasPolynomialCost` |

The geometric domains include $c\ge1$, $c/N\le1/3$ for near cancellation,
and $2(e+3)cB\le N$ for logarithmic linearization. These inequalities must
be retained when assembling a simultaneous overlap-horizon estimate.

Every completed conductor has the actual lower floor
\[
E_m(c)\ge \frac{2\,\mathrm{tiltedSplineTailConstant}}{\int\phi^2}\,c^{-7},
\qquad c\ge1.
\]
Its Möbius formula is
\[
E_m(c)=\frac1{\varphi(m)}\sum_{d\mid m}\mu(m/d)d E_1(c/d).
\]
Since $E_1(y)\le C y^{-7}$ for $y\ge1$, each fixed conductor also has an
upper bound $E_m(c)\le C_m c^{-7}$ for $c\ge m$. Thus the energies of any
fixed finite conductor family have bounded ratios as overlap grows.

The target is an actual relative residual estimate and a simultaneous
positive finite-packet range along an explicit unbounded overlap schedule.
Fixed-packet positivity does not control all growing horizon directions.
Full eventual positivity at $c_N=2(\log N)^\alpha$, $\alpha>1/4$, remains
the separate RH-equivalent endpoint.

The sharper upward-source target retains
$c^{10}(\log N/N)^2+c^6/\sqrt{\log N}$ in squared norm. Combining all eight
terms and dividing by the squared conductor floor would give
\[
\frac{\|A_{c,N}r_{m,N}-E_m(c)r_{m,N}\|^2}{E_m(c)^2}
\le C_m\left[c^{24}(\log N/N)^2+c^{20}/\sqrt{\log N}\right].
\]
Both terms vanish for $c_N=(\log N)^\alpha$, $0<\alpha<1/40$.
This is a relative-quasimode target, not yet a proved source theorem.
Finite-packet positivity also requires the Gram error after multiplication
by the varying energies. The quadratic energy bound
$|E_m(c)|\le C_m c^2$ reduces that separate payment to a quantitative
Gram estimate against the $c^{-7}$ floor. A fixed-parameter Gram limit
alone does not supply it.

The literal Ramanujan Gram has the conductor-explicit bound
\[
\left|\sum_{n\le N}r_m(n)r_l(n)-\delta_{ml}H_N\right|\le2ml,
\qquad |H_N-\log N|\le1.
\]
For a finite conductor family $S$ and arbitrary real coefficients $b_m$,
the logarithmic Gram discrepancy is at most
$(1+2\sum_{m\in S}m^2)\sum_{m\in S}b_m^2$.
Source: `SignedArithmeticHodgeTheory/GrowingRamanujanFamiliesHaveAUniformGramBudget`.
Combined with the quadratic energy ceiling, its scaled mixed-entry payment
is $O_S(c^9/\log N)$, which vanishes throughout $0<\alpha<1/40$.

Lean residual target: `CompletedArithmeticForms/WeilPolynomialResidual.lean`.
