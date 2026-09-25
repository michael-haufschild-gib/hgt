# Frozen continuous Green-source experiment

Question: was the failure of positive zero-preserving source dressing caused by discrete periodic tails, or does it survive continuous kernels? For an actual arithmetic source Phi_h, set Psi_a(z)=integral_R exp(-a*|u|)Phi_h(z-u)du, a=.5 or1.5. Its Fourier multiplier2a/(a^2+w^2) has no zeros and no poles in |Im w|<.5. The source remains positive/even on the real axis when the original source is. Full-source positivity for D/L5 is not newly proved by this experiment. For a=.5,b=1.5, composition is (K_a*K_b)*Phi=1.5Psi_a-.5Psi_b, a positive convolution represented by a difference. Retain both terms; cancellation is not optional. The transform relation and positivity reasoning are derived controls, not experimental discoveries or newly audited Lean proofs.

Objects: R uses Phi_R(z)=sum exp(z/2)(4q_n^2-6q_n)exp(-q_n),q_n=pi*n^2*exp(2z). B4,L5,D are the previously independently verified theta sources in source.py: periods4,5,5; parities1,0,1; D coefficients[0,1,k,-k,-1],k=(sqrt5/2-sin(2pi/5))/sin(4pi/5). Actual D is distinct from the finite fake coefficient witness in the corpus. No source data is discarded.

Computation uses Psi_a(z)=exp(-az)(M_a-U_+(z))+exp(az)U_-(z), where M_a=integral_R exp(ax)Phi_h(x)dx and U_+-=integral_z^infinity exp(+-at)Phi_h(t)dt. M_a is computed by the verified symmetric real-source quadrature at h=1/64,|x|<=3.5. Upper tails are evaluated termwise by incomplete gamma functions in |Im z|<pi/4. For R use v=(.5+-a)/2 and .5*b_n^(-v)[4Gamma(v+2,q_n)-6Gamma(v+1,q_n)]; other hosts use v=(parity+.5+-a)/2 and c_n*n^parity*b_n^(-v)Gamma(v,q_n). The analytic identity Psi_a''=a^2Psi_a-2aPhi_h supplies derivative checks. At a=.5, R has independently derived closed expression .5exp(-z/2)-exp(z/2)sum exp(-pi*n^2exp(2z)); this checks implementation only. It is not a new discovery.

Four hosts times3kernel choices=12cases. Each uses8 real starts0,.12,.3,.55,.9,1.3,1.9,2.5 crossed with8imaginary starts.15,.35,.5,.62,.7,.75,.78,.784. Search domain|Re z|<3.5,0<|Im z|<pi/4;44Newton iterations,stepcap.15,normalized residual and correction below1e-28. Keep every failed start. This is not a complete root count. Preparation and all workers share575cooperative/585hard seconds pluscleanup<10. Pilot and known identities cannot be labeled discoveries. Any selected witness requires100/160digits, larger source-moment quadrature and an independent forced-ODE/Jacobi integral. No Lean builds.

Adversarial admission: positivity, multiplier nonvanishing, simple pole cancellation, small-perturbation zero continuity and generic nonreal source zeros are foreseeable. Discovery target is whether continuous smoothing provides a full-strip logarithm candidate that discrete dressing failed to provide, and whether any difference separates literal arithmetic hosts from actual D. Finding a stable interior node kills a specific candidate; no finite failure to find one establishes a route. Gaussian smoothing was rejected because G_t(z)=exp(-z^2/(4t))/sqrt(4pi*t)*F_{-1/(4t)}(-iz/(2t)), with F_lambda(w)=integral Phi(x)exp(lambda*x^2)exp(iwx)dx; naive source-node scanning repackages backward deBruijn flow.

Current corpus audit: cached deep searches are partial/source-only. Relevant primitives include SchwartzMap.fourier_convolution, RiemannGaussian.gaussianSmoothing_apply/even and RHTower.gaussianSmoothing_fourier. These do not by themselves establish this full Green-source analytic bridge. No new formal theorem/axiom audit is claimed. All HB SS/SV/VV, temporal reader, remainders and physical boundaries are outside this arithmetic experiment, not zeroed.

Broad recent inspiration: Cao,Chen,Qiu, Homogenization of anisotropic diffusion on pre-Sierpinski carpets, arXiv2609.04936v1,4September2026, https://arxiv.org/html/2609.04936v1 (abstract/introduction read). Their result distinguishes microscopic anisotropy from limiting isotropy under specific symmetry/heat-kernel conditions. Borrow only the question whether a discrete structural obstruction survives a continuous representation; none of their theorems applies here. Broad cloaking searches also found quantum-detectability work but supplied no applicable theorem.

Whole-route meaning: source-logarithm feasibility is a prerequisite of one proposed approach, not an RH selector by itself. A surviving representation must still distinguish actual off-line zeros and connect to a global spectral theorem. A failure should redirect attention toward invariants of the source/multiplier pair rather than literal source zeros alone.

## All24 operations

1. **Split**: Separate original source, individual continuous resolvents and their positive composition.
2. **Falsify**: Search complex source zeros; one validated interior witness kills a full-strip logarithm for that host and kernel.
3. **Reverse**: Apply (alpha^2-D^2)Psi=2alphaPhi as control, preserving all derivative and tail terms.
4. **Viewpoint**: Keep spectral zeros but change the positive source representation; distinguish arithmetic function from source coordinates.
5. **Visual**: Save root map for12 host/kernel combinations; compare with discrete-tail witnesses.
6. **Action**: Apply Laplace kernels atalpha=.5,1.5 and their composition to each of4 arithmetic hosts.
7. **Essentials**: Retain full theta source, total exponential moment, both upper incomplete-gamma tails and all partial-fraction terms.
8. **Similar**: Use zeta, primitive conductor4/5 and actual Davenport-Heilbronn as separately verified hosts.
9. **Small**: Single resolvent is minimal; original differential identity is control, not discovery.
10. **Extreme**: Composition removes two spectral pole pairs from reciprocal multiplier; inspect near source-strip boundary and both real tails by symmetry.
11. **Experiment**: 60digit pilot/control gates and12cases,14workers maximum,one600second cap. Selected surprises require100/160independent ODE/Jacobi validation.
12. **Invariant**: Fourier multipliers2alpha/(alpha^2+w^2) have no zeros or interior RH-strip poles; convolution preserves real positivity/evenness.
13. **Monotone**: Do not assume smoother source has fewer complex zeros or composition improves the logarithm domain.
14. **Weaker bridge**: Finite interior node witnesses only; no root found cannot certify nonvanishing.
15. **Stronger hunch**: Continuous kernel might remove discrete Floquet obstruction; test whether a different complex-source obstruction remains.
16. **Minimal counterexample**: Compare composition against both constituent resolvents for same host.
17. **Representation**: Compute via upper incomplete-gamma tails; validate with forced ODE and independent Jacobi source.
18. **Technique**: Current deep/source-method hits support convolution and Gaussian heat primitives but not this complete bridge. Homogenization paper suggests testing microscopic structure versus limiting representation.
19. **Fake proof**: Same spectral zeros and positive source do not entail RH or holomorphic source logarithm.
20. **Missing lemma**: Global nonvanishing of an admissible source representation and a source-specific real-rootedness theorem; either may fail.
21. **Dependency**: Verified arithmetic host -> convergent Green convolution -> exact spectral multiplier -> numerical source nodes; no HB action attachment.
22. **Nearby false**: Gaussian-source convolution is exactly a rotated/rescaled backward deBruijn deformation; naive scanning was rejected as a repackaging.
23. **Boundary**: Retain multiplier poles at+-i alpha and noncompact source tails; source evaluation confined to |Im z|<pi/4.
24. **Salvage**: If all tested Green sources retain nodes, abandon generic resolvent removal and identify representation-invariant information required of a source-to-spectrum mechanism.
