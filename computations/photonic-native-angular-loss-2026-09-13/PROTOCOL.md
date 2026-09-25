# Frozen angular-average scalar-reader experiment

## Question and prediction attempt

The native ideal-lattice squeeze ensemble has a scalar hyperbolic diffusion generator. Does an actual finite-energy monitored optical encoding retain scalar rejection rates after physical pump orientations are averaged, or does a logical matrix potential survive? A scalar rate must be independent of the logical input state. This is a necessary condition for the proposed scalar reader, not a sufficient scattering identification.

The complete physical-loop experiments found high survival with nontrivial logical response. They do not decide this question. An attempted symmetry proof fails because averaging lab-frame squeeze orientations does not twirl an irreducible logical symmetry group inside a fixed code. A dense-lattice Gaussian approximation predicts a scalar fixed-shape limit, but prior coupled-cusp/phase experiments show why uniformity cannot be assumed. The finite coupled-cusp operator spectrum is therefore unresolved by either argument. This is an exploratory falsification target, not a universal law selected for provability.

## Mathematical objects and physical controls

Set [q,p]=i, H0=(q^2+p^2)/2, E_delta=exp(-delta H0). At shape g=M(x,y)=[[1/sqrt(y),x/sqrt(y)],[0,sqrt(y)]], prepare Psi=E_delta U(g)comb and W=Psi(Psi^*Psi)^-1/2. Comb_j(q)=sum_n exp(2*pi*i*b*n)delta(q-sqrt(2*pi*d)*(n+(j+a)/d)), with a=b=0for d2 and a=b=.5for d3. Every Gram eigenvalue is retained.

A pump kick is M_theta=R_theta diag(exp(ell/2),exp(-ell/2))R_theta^-1. Such a squeeze is obtained from positive-permittivity quarter-wave segments, with compensating rotations and a removable central sign on the base. Actual quantum evolution U(M_theta) is used, followed by the code projector at M_theta g. Its projected logical amplitude is K_theta=W_target^*U(M_theta)W. The source Gaussian matrix is M_theta C_delta g; the target is C_delta M_theta g. Their order is never exchanged. An overall metaplectic sign cannot change K_theta^*K_theta; short-step continuation is retained anyway. No monitor is inserted inside the kick's optical control sequence.

Compute L_theta=(I-K_theta^*K_theta)/ell^2 and its uniform angular mean Lbar. Its eigenvalues give the loss rates of extremal logical inputs. Save the full Hermitian matrix, eigenvalues, relative traceless Frobenius norm, mean rate Tr(Lbar)/d and canonical-mixture rate Tr((G/TrG)Lbar). This directly compares two preparations without replacing a matrix by a trace. Scalarity requires equal eigenvalues, not just a stable mean. Logical transport and physical bases are additional unresolved channels even if this loss turns out scalar.

## Frozen portfolio and discrimination

Use x=.3, d2/3; (y,delta)=(1,.2),(1,.05),(4,.2),(4,.05),(16,.05),(64,.0125). Cross ell=.002/.001 with8/16 equally spaced angles in[0,pi). Total48tasks. The last three cusp points with(y,delta)=(4,.2),(16,.05),(64,.0125)hold delta*y=.8. N=ceil(5sqrt(y/(delta*d)))+4per comb. No zeta values, roots, prime positions or spectral fits enter the experiment.

One600secondwhole-family guard with14workers,native threads1,3GiB/process,2GiBscratch. First full compact case sizes the job; stop above60sor failed unitarity/loss controls. Initial complex128loss subtraction is cancellation-sensitive. Negative loss below-1e-5fails immediately. No discovery is validated merely because it passes that permissive floating-point gate. Selected unequal eigenvalues must survive smaller kick/angle refinement and independent50/100/160digit Jacobi/full-kernel evaluation with larger sums. Partial outputs and all control failures are retained. No continuum or interval proof is claimed.

A phase-independent scalar fixed-shape Gaussian loss would be a known candidate approximation, not a headline. Its numerical value must not be confused with Re(u)=1/4in the Riemann receiver: a local rejection coefficient and a complex spectral coordinate are different quantities. The target is presence or absence of a matrix-valued obstruction at the cusp, not optimizing an attenuation constant.

## Whole-route consequence and sources

Unequal eigenvalues mean that two logical states at the same base lattice have different averaged survival. A scalar probability process on lattice shape then fails to describe this reader without retaining additional fibre data or justifying a different preparation/measurement. The positive survivor is a bundle-valued diffusion with a measured matrix loss potential, which could still have an interesting arithmetic response. Scalarity would remove one local obstruction but prove neither global cusp scattering nor RH confinement.

The ideal local Casimir derivation uses group identities visible in arXiv2605.28243; its compact global theorem is not applied. GKP phase/finite-energy context comes from arXiv2410.07332and2605.28784. Broad recent searches for averaging/Casimir/thermalization found rotation synchronization(arXiv2602.10115), a deformed relativistic oscillator(arXiv2603.06637), and a micromaser topology reader(arXiv2607.21299). Their spaces and dynamics differ from this problem; none supplies a transferred theorem. The retained methodological point is to inspect the measured response channels rather than assume a topological label fixes them.

Current cached deep search is partial with pending coverage. The inspected RydbergClockDephasing source gives a double-commutator identity for an involutive clock satisfying U^2=1. That is not our continuous physical-angle average and cannot force scalarity here. No Lean build or new formal theorem. Material dispersion, pump backreaction, detector implementation, global scalarization, primitive cusp normalization and RH-independent selection remain open.

## All24methods

1. **Split**: Separate scalar base diffusion, logical connection and state-dependent rejected probability. This experiment tests only the last, a necessary scalar-closure condition.
2. **Falsify**: If the angularly averaged loss has unequal eigenvalues after refinement, survival depends on the logical input; a scalar base Markov reader alone is insufficient for these encodings.
3. **Reverse**: Assume a scalar optical diffusion reader exists; it must have the same infinitesimal rejection probability for every logical input at fixed lattice shape.
4. **Viewpoint**: Promote discarded measurement probability to an operator potential on the optical lattice bundle; do not normalize it away.
5. **Visual**: Compare the smallest/largest averaged-loss eigenvalues on compact and coupled-cusp states, paired by code dimension.
6. **Action**: Apply the actual unitary squeeze, then project onto the canonically re-prepared finite-energy code. Average physical pump orientations, not logical bases.
7. **Essentials**: Retain all Gram directions and invariant displacement phases. No state-dependent attenuation or finite-energy envelope term is dropped.
8. **Similar**: Compare d2even and d3odd phase-correct codes; uniform-logical and canonical-mixture averages are read from the same full operator.
9. **Small**: First compact d2case sizes the job. Unitary-kernel and positive-loss checks are expected controls, not discoveries.
10. **Extreme**: Use y1,4,16,64 and delta.2,.05,.0125, including three points on delta*y=.8. No infinite-limit inference from them.
11. **Experiment**: 48jobs with14workers andone600secondcap. Cross two kick lengths and two angle quadratures; independent selected50/100/160validation required.
12. **Invariant**: Eigenvalues of K^*K are source-frame gauge-invariant. Angular isotropy on the base is not a logical Schur-lemma hypothesis.
13. **Monotone**: No assumption that angular averaging reduces logical anisotropy monotonically or that smaller delta gives a uniform cusp limit.
14. **Weaker bridge**: The local averaged ideal squeeze generator is a hyperbolic Laplacian. This bridge does not establish scalar closure of a monitored quantum reader.
15. **New hunch**: Exploratory candidate: physical angular averaging removes the logical dependence of the infinitesimal loss even at the finite-energy cusp. The previous full-loop maps do not decide it; no universal RH law is claimed.
16. **Minimal counterexample**: Two eigenvectors of one averaged loss operator with different rejection rates suffice to disprove that local scalar-closure identification.
17. **Representation**: Compute Gaussian-kernel cross-Grams, then L=(I-K^*K)/ell^2; save every angular matrix and both state averages.
18. **Technique**: Combine Lie-group phase averaging with the exact physical/projected transport used in the validated loop family. Broad recent rotation/thermalization papers do not supply an applicable optical-lattice theorem.
19. **Fake proof**: The pump orientation is averaged, hence Schur lemma makes the logical loss scalar. Gap: physical rotations move the lattice and do not act as an irreducible symmetry within its fixed logical fibre.
20. **Missing lemma**: Scalar survival closure of the finite-energy phase-correct optical encoding under isotropic native Floquet transport, uniformly at a cusp.
21. **Dependency**: Native squeeze ensemble -> lattice-base diffusion -> quantum transport/measurement loss -> scalar or bundle-valued response -> primitive cusp scattering -> independent RH confinement.
22. **Nearby false**: Dropping the rejection branch or replacing the full loss matrix by its trace would force scalarity by definition. Both are forbidden.
23. **Boundary**: Both code phases, all logical weights, heat envelope order and exact stroboscopic symplectic propagation retained. Pump/control micromotion is unmonitored inside each kick; global central phase cannot affect loss.
24. **Salvage**: A nonscalar result identifies the local matrix killing potential required by a physical response. A scalar result removes one obstruction but leaves logical connection, global cusp conditions and RH selection open.
