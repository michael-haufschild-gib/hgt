# Which optical lattice really has the modular quotient?

Status: explicit algebraic bridge candidates and next experimental gate; not newly Lean-formalized. The numerical metric families so far use a fixed zero-phase section and do not resolve this gate.

Let two displacement vectors v1,v2 have symplectic area 2*pi*d. With the Weyl convention D(v)D(w)=exp(-i*Omega(v,w)/2)D(v+w),

    D(v1+v2)=(-1)^d D(v1)D(v2).

If a code has stabilizer eigenvalues (eta1,eta2), relabeling its basis by T:(v1,v2)->(v1,v1+v2) changes the eigenvalue labels to

    (eta1, (-1)^d eta1 eta2).

The basis move S:(v1,v2)->(v2,-v1) gives (eta2,eta1^(-1)). These follow by operator multiplication; neither transformation is a numerical discovery.

Consequences for the construction:

* For even d the (+1,+1) choice is preserved by these generators.
* For odd d the (+1,+1) choice is not preserved by T. A metric calculation in that fixed section cannot automatically be interpreted as a scalar function on the full modular surface.
* For odd d the (-1,-1) choice is preserved by both generators. It supplies a candidate invariant phase section. This does not remove logical/metaplectic holonomy or prove that the physical response is the scalar modular Laplacian.

The zero-phase ideal comb used in the first computations is

    comb_j(q)=sum_n delta(q-L*(n+j/d)), L=sqrt(2*pi*d).

A useful explicit phase family is

    comb_j^(a,b)(q)=sum_n exp(2*pi*i*b*n)
                                  delta(q-L*(n+(j+a)/d)),

where a,b are0 or1/2 for the four sign choices. The odd invariant choice is a=b=1/2. Its geometry can be tested with exactly the same physical symplectic propagation and finite-energy envelope as the original family. Thus no zeta-dependent dielectric or arithmetic source is needed.

Another tempting shortcut needs a separate audit. In the distributional stabilizer expansion, uniformly averaging the UNNORMALIZED ideal projectors over their entire phase torus leaves only the identity Fourier component. Applying a common exp(-delta H0) envelope on both sides then produces a thermal operator proportional to exp(-2delta H0), which loses lattice-shape information. This statement is a formal bridge candidate requiring analytic justification for ideal projectors; it is not a claim about averaging individually normalized finite-energy states, which is a different prescription. Full phase averaging cannot simply be assumed to preserve an arithmetic receiver.

The next discriminating experiment is phase choice times cusp approach times reader: compare zero phase, the odd invariant phase, and the other half-phase sectors at the same d, lattice shape and finite-energy prescription. Cheap S/T consistency checks validate the representation; the unknown target is the physical end geometry after retaining the phase information required by the modular quotient. If correcting the phase section changes the putative scattering end, the original metric was attached to an incomplete physical object. If it does not, the finite-energy boundary law remains the main obstacle. Neither outcome is a statement about Riemann zeros before the response operator is identified.

The two planes must also stay distinct. tau=x+iy labels a lattice shape. u labels the spectral scaling of waves on the space of shapes. Riemann's parameter is s=2u in the proposed cusp receiver. Zeros would be resonances of that response, not points of the tau-plane; the RH line Re(s)=1/2 corresponds to Re(u)=1/4, not to the unitary scattering line Re(u)=1/2.

Evidence: Weyl displacement/lattice definitions in [Conrad–Burchards–Flammia](https://arxiv.org/html/2407.03270v2), and the phase-torus bundle in [Burchards–Flammia–Conrad](https://arxiv.org/html/2410.07332v2). Current phase-fibre corpus search was partial/source-only and supplied no applicable checked continuum theorem. No Lean builds or changes.
