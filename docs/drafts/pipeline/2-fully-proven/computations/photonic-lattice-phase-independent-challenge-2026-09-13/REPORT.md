# The optical lattice phase changes the cusp object

This numerical family changes physical stabilizer signs before computing optical state geometry. It contains no zeta input and proves no RH statement.

## Objects and question

Take an oscillator with [q,p]=i and dim-d lattice code columns comb_j^(a,b)(q)=sum_n exp(2*pi*i*b*n)delta(q-L*(n+(j+a)/d)), L=sqrt(2*pi*d). The finite-energy encoding is Psi=exp(-delta H0)U(R(theta)M(x,y))comb with H0=(q^2+p^2)/2 and M=[[1/sqrt(y),x/sqrt(y)],[0,sqrt(y)]]. Use all logical columns and full Gram matrices. Compare the support projector Psi(Psi^*Psi)^-1Psi^* against the canonical mixture PsiPsi^*/Tr(Psi^*Psi). Their full3D Grassmann/Bures metrics and the separately chosen rotation Schur complements Q are saved.

The Weyl law gives D(v1+v2)=(-1)^d D(v1)D(v2). For basis relabeling T:(v1,v2)->(v1,v1+v2), stabilizer eigenvalues change to(eta1,(-1)^d eta1 eta2); S gives(eta2,eta1^-1). Hence the constant(+,+)section is invariant for even d, while the constant(-,-)section is invariant for odd d. A fixed odd(+,+)code is not automatically a scalar object on the full modular quotient. These are derived algebraic bridge candidates, not newly Lean-formalized theorems.

H3 was frozen: the correct modularly invariant phase might restore a common hyperbolic cusp geometry. Four half-phase choices a,b in{0,.5}for d1/3, and even d2,a=b=0, were compared at x=.3, delta*y=.2/.8, delta.1/.05. The proposed hyperbolic marked tensor requires Qxx/Qyy=1, zero cross term and constant y^2 sqrt(det Q). No change of coordinates or global curvature theorem is inferred from these ratios.

## Outcome

All36production tasks completed. Six structural configurations were independently evaluated at100/160working digits with infinite inner Jacobi summation, twice outer truncation, smaller derivative steps and direct complex SVD for density fidelity. All12challenge tasks passed, including full-tensor positivity and agreement criteria.

Maximum100/160tensor component discrepancy divided by max(component magnitude,1e-8):1.74e-13; production/challenge discrepancy:1.74e-09. The invariant S/T fidelity controls passed; they validate a known identity rather than constitute an experimental discovery. Working digits are not accurate derivative digits or interval certificates.

| d | (a,b) | y | delta | Support Qxx/Qyy | Mixture Qxx/Qyy |
|---|---|---:|---:|---:|---:|
|1|(0,0)|16.0|.05|5.88777725037|5.88777725037|
|1|(.5,.5)|4.0|.05|0.95187110674|0.95187110674|
|1|(.5,.5)|16.0|.05|0.00693165147864|0.00693165147864|
|3|(.5,.5)|4.0|.05|0.832561523374|0.913885080443|
|3|(.5,.5)|16.0|.05|0.00379308434375|0.0157426672057|
|2|(0,0)|16.0|.05|0.00693165147864|0.0418985709709|

For d1 at y16,delta.05, changing the incorrect global(+,+)section to the invariant(-,-)section changes the ratio from5.88777725 to.00693165148. For d3 the mixture ratio changes from about.17600730 to.01574266721. The earlier opposite behavior of odd versus even codes therefore cannot be attributed to code dimension alone: the missing phase matters. Nevertheless, the invariant sections remain strongly anisotropic in the tested cusp regions. H3 does not rescue a finite-energy standard-hyperbolic metric identification; no infinite-limit no-go is claimed.

## Positive survivor and meaning for RH

The physical state space is a lattice with phase data, not merely a lattice drawing. Correcting the phase is necessary before assigning a full modular quotient. The surviving construction uses native hyperbolic Floquet action on the ideal lattice quotient, which is conjugate to a sample of modular geodesic flow; this does not require the distinguishability metric to be hyperbolic. The next question is the transport/reader operator on the full lifted encoding.

This preparation uses E_delta U(g); a real temporal pump evolves it as U(F)E_delta U(g). The energy envelope must be transported or its reset measured explicitly. Global metaplectic phases cancel in the current density/support measurements, so these results do not identify an absolute scalar cusp character. Primitive normalization, physical scattering generator, cusp boundary law, full material/pump dynamics and RH-independent confinement of the relevant modular resonances remain unestablished.

On the standard scalar modular surface Riemann zeros rho correspond to resonances u=rho/2; RH would require Re(u)=1/4. That line is different from the unitary scattering line Re(u)=1/2. Neither phase-correct modular closure nor any measured metric proves confinement.

Primary framework: arXiv2407.03270,2410.07332,2605.28784. Cached current corpus searches were partial/source-only; finite-column fidelity and gauge identities are not continuum optical scattering formalizations. No Lean builds, HB action claim, historical novelty assertion or proof status from this directory name. All24method applications, raw matrices, phases, sums and validation outputs are retained.
