# Frozen stabilizer phase times photonic cusp experiment

H3: the stabilizer-phase section required for the full modular quotient may restore a common hyperbolic cusp geometry. This is a new hunch, not a redefinition of H1/H2. Its motivation is structural: the first code metric used a zero-phase section; Weyl phases show that section is not invariant under the full modular group for odd code dimension. The unknown is whether correcting the physical object changes its end geometry, not whether S/T identities hold.

Native states: comb_j^(a,b)(q)=sum_n exp(2*pi*i*b*n)delta(q-L*(n+(j+a)/d)), L=sqrt(2*pi*d), j=0,...,d-1. Propagate by the same M(x,y), physical rotation and canonical exp(-delta H0) as earlier families. All four a,b in{0,1/2} tested for odd d1/3; d2,a=b=0 control. This is a local family of full optical displacement stabilizers. Neither zeta nor its zeros occurs in model or parameters.

Derived Weyl control: if stabilizer eigenvalues are(eta1,eta2), T basis change gives(eta1,(-1)^d eta1 eta2), S gives(eta2,eta1^-1). Thus(+,+) is invariant for even d, and(-,-) for odd d. Under odd d, an arbitrary fixed(+,+) section cannot be assigned to the full scalar modular quotient. These algebraic facts are bridge candidates, not newly Lean-proved results or discoveries from this computation. Source is the Weyl displacement law in arXiv2407.03270 and full phase bundle in arXiv2410.07332. Cached deep search was partial/source-only with no applicable continuum GKP result.

Implementation: add phase weight -2*pi*i*b_left*n to each outer overlap term, and +2*pi*i*b_right*m to inner terms. With shifted inner coordinate t=m+(j+a)/d, modify linear exponent by2*pi*i*b_right and constant by-2*pi*i*b_right*(j+a)/d. Phase weights are retained in wave() as well as analytic overlaps. Physical generator controls compare base code to T:(x+1,y,theta0), and S:(-x/|tau|^2,y/|tau|^2,theta=-arg(tau)), since M(tau)S=R(-arg(tau))M(-1/tau). Root fidelity must equal1 within1e-20for the predicted invariant sections; noninvariant sections are controls, not failures by definition. Global phase cancels from these density/projector readers; a phase-sensitive dynamical reader remains outside this test.

Measure both full3D metrics, rotation quotients, Gram/density spectra, purity and modular-generator root fidelities. Same36case portfolio: four half-phase sectors for d1/3, one for d2, crossed with delta*y=.2/.8 and delta.1/.05. x=.3,50working digits, h1e-6,N=ceil(4sqrt(y/(delta*d)))+3. First complete case is sizing pilot inside same600secondcap;14workers/native threads1; preserve partials. No interval certification or global cusp theorem. Selected surprises require100/160digits, larger sums/smaller steps and independent inner Jacobi summation.

Broad recent quantum-geometry/fidelity literature has already shown why phase orientation and anisotropic metrics should be retained; no cross-field theorem is transferred. Primary GKP phase-bundle information is needed for model applicability. No arbitrary twist was selected to align with a zeta zero. Full material/pump dynamics, physical response generator, primitive cusp normalization and RH-independent resonance confinement remain unknown. Finite-energy symplectic geometry alone does not prove a spectral statement.

Big-picture decision: a wrong phase section can prevent Riemann's scalar modular geometry from ever being the right native object. Correcting it either exposes a surviving geometric receiver candidate or shows that its physical end still differs from the standard arithmetic model. In either case the research learns which physical object must be studied, not an optimized numerical constant.

## All24 methods

1. **Split**: Four stabilizer-sign sections, odd dimensions1/3 and invariant even-dimension2 control; both projector/density metrics.
2. **Falsify**: Test whether the phase section needed for the full modular quotient eliminates the observed cusp anisotropy. Failure leaves physical boundary law open.
3. **Reverse**: Given the desired modular quotient, derive phase transformation from Weyl law before imposing a scalar reader.
4. **Viewpoint**: Use the full optical displacement group rather than its bare lattice drawing; phase is physical data.
5. **Visual**: Display phase-sector ratio maps with invariant-section markers and generator fidelities.
6. **Action**: Change stabilizer phases while holding shape, area, energy envelope and reader fixed; combine with cusp approach.
7. **Essentials**: Retain every Weyl sign in both comb sums and all logical channels; no phase average substituted.
8. **Similar**: Odd d1/3 each compare all four half-phase choices. Even d2 zero-phase section is a structural control.
9. **Small**: First full case is sizing pilot; generator S/T fidelity checks are predicted implementation tests only.
10. **Extreme**: Two fixed delta*y paths at delta.1/.05; both cusp depth and finite energy change. No infinite-limit theorem claimed.
11. **Experiment**: 36cases with14workers under one600secondguard; adverse selected results need100/160independent summation.
12. **Invariant**: Weyl law D(v1+v2)=(-1)^d D(v1)D(v2) fixes which constant sign section is invariant under S/T.
13. **Monotone**: No claim that symmetry restoration monotonically improves metric anisotropy or scattering.
14. **Weaker bridge**: Modular-generator closure is only a kinematic bridge and does not replace the unknown physical scalar operator.
15. **New hunch**: H3 frozen: retaining the modularly invariant stabilizer phase may restore a common hyperbolic cusp geometry. This is independent of H1/H2 and cannot redefine them.
16. **Minimal counterexample**: Same d,shape and delta with only one sign flipped isolates the missing data.
17. **Representation**: Gaussian kernel/comb with explicit phase factors; S/T controls compare equivalent lattice bases in actual symplectic charts.
18. **Technique**: Weyl multiplication and phase-torus bundle from primary GKP literature; current cached search supplies no checked continuum theorem.
19. **Fake proof**: A lattice and its relabeled basis define the same zero-phase code for every d. Odd-d Weyl sign is the exact gap.
20. **Missing lemma**: A justified phase/readout sector whose full photonic response is the scalar modular cusp receiver.
21. **Dependency**: Quantum commutation -> symplectic integral lattice -> phase-correct modular identification -> physical metric/response -> resonance law.
22. **Nearby false**: Uniform phase averaging may destroy lattice information; do not treat it as a harmless gauge quotient. Individually normalized phase mixtures differ from unnormalized averaging.
23. **Boundary**: Keep all phase weights, logical Gram spectra, rotation, energy envelope and sum/derivative resolution.
24. **Salvage**: If invariant phase does not fix end geometry, retain correct quotient and stop using wrong phase sections; identify the remaining physical metric as the next object.
