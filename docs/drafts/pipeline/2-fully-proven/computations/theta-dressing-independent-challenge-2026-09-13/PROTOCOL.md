# Frozen positive geometric dressing of the literal theta source

Question: can a positive change of representation remove the complex source zeros obstructing a global source logarithm without moving the zeta zeros in the RH strip? Competing explanations: central zeros disappear globally; central zeros only migrate; or an asymptotically periodic tail restores infinitely repeated obstructions. Root searches discriminate particular witnesses, never certify global absence.

Let Phi(z)=sum_{n>=1} exp(z/2)(4q_n^2-6q_n)exp(-q_n), q_n=pi*n^2*exp(2z). Let L=log(p), r=p^(-alpha), and Psi(z)=sum_{k in Z} r^|k| Phi(z+kL), p>1, alpha>=1/2. Each real summand is positive and reflection pairs preserve evenness. Direct absolute-convergence/Fourier-shift reasoning gives the geometric multiplier (1-r^2)/(1-2r*cos(wL)+r^2). Its only poles are w=2pi*n/L +-i*alpha, and it has no zeros. Consequently the open RH strip |Im w|<1/2 retains the original spectral zeros if this transform bridge is justified analytically. This algebra is a derived control, not an experimental discovery or newly audited Lean theorem. Psi has exponential rather than superexponential tails: they may not be truncated at the old theta window.

Tail candidate H(z)=sum_{j in Z} r^(-j)Phi(z+jL) satisfies H(z+L)=r H(z); exp(alpha*z)H(z) is periodic. For z=u+mL, r^(-m)Psi(z) tends to H(u). Seek H nodes in one fundamental cell, then challenge the first qualifying node against actual Psi near z+8L and z+16L. Whether H has nodes is not inferred from these identities. This is the unknown, not the expected translation once a tail node exists. Psi controls use (1+r^2)Psi(z)-r(Psi(z+L)+Psi(z-L))=(1-r^2)Phi(z). This recurrence and H quasi-periodicity are cheap implementation checks.

Production compares p=2,3,5,7,4,6,2.5 and alpha=.5,1 for both full source and tail (28 independent cases). Prime versus composite/noninteger distinctions are controls on arithmetic specificity; only prime alpha=.5 receives the Euler-factor interpretation. Each case has48 fixed Newton starts: six real fractions and eight imaginary heights .2,.4,.55,.65,.72,.76,.78,.784. Full-source real search is0..2.5, tail search is one fundamental cell. Domain |Re z|<3 for full source and |Im z|<pi/4 with lower cutoff. Tail coordinates are reduced modulo L after Newton steps. A bound on summed scaled terms and Newton correction rejects false tiny Gaussian-tail roots. Complex roots always require subsequent100/160digit validation with independent Jacobi evaluation, wider shift truncation and local numerical winding.

Cutoffs: precision-dependent theta term budget inherited from validated literal source (1500 cap); shifted-source window C=.5log(((dps+90)log10)/(pi*cos(2Imz)))+2, plus one shift on each side. Far-tail calculations rescale by exp(alpha*Re z) to avoid underflow. This is a conservative numerical cutoff, not an interval enclosure. Embedded pilot measures a fixed subset before full launch and shares its deadline.14processes; native threads1;575second cooperative/585hard guard with cleanup under10seconds. Seeds deterministic. All failed starts and partial results retained. No Lean builds.

Current corpus searches are cached, partial and source-based. The available Euler-geometric-series and convolution statements support mechanism discovery but were not found to provide this complete source/Fourier bridge; no absence or unconditional formalization claim. Source/normalization provenance comes from the earlier independent theta/Jacobi controls. All SS/SV/VV, native physical remainder, onset and boundary work are outside this arithmetic experiment, not silently dropped terms.

Broad recent input: Kovner,Lublinsky,Nefedov,Skokov, Running coupling effects in the anti-collinear resummation in high energy evolution, arXiv2607.09337v1 (10July2026), https://arxiv.org/html/2607.09337v1; abstract/introduction read. Methodological lesson only: changing a kernel/resummation representation requires retaining the coupled changes and testing the relevant observable. No QCD result applies to theta. NIST DLMF20.2, https://dlmf.nist.gov/20.2, provides the independent Jacobi representation.

Big picture: this targets whether complex-source geometry is an intrinsic obstacle to the zeta spectrum or a removable feature of one positive representation. A successful finite witness can kill one logarithm-based candidate while preserving the underlying zeta problem; absence of witnesses cannot create an RH route. Positive salvage must identify which representation features survive and which source-to-spectrum mechanism is still missing.

## All24 operations

1. **Split**: Compare full positive dressed source with its rescaled far-tail periodization; distinguish source zeros from Fourier zeros.
2. **Falsify**: Hunt source zeros in both central window and tail fundamental cell; independent validation follows any claimed obstruction.
3. **Reverse**: Apply the exact difference operator recovering literal Phi; use it only as a control, not a discovery.
4. **Viewpoint**: Change positive-source representation while analytically preserving the spectral zeros inside the RH strip.
5. **Visual**: Save source root positions and repeated far-tail witnesses for a strip map.
6. **Action**: Vary shift base and decay; compare actual source versus its tail limit.
7. **Essentials**: Retain all geometric shifts to a precision-dependent cutoff, all theta terms, exponential source tails, and multiplier poles.
8. **Similar**: Compare primes2,3,5,7 with composites4,6 and noninteger2.5. No automatic Euler interpretation for controls.
9. **Small**: A single geometric shift operator is the minimum intervention; alpha1 and alpha.5 are fixed distinct regimes.
10. **Extreme**: Search near the source analytic boundary and test roots translated by8 and16 shift lengths.
11. **Experiment**: Embedded60digit pilot, then28 cases under one600second cap;14workers maximum. Selected roots require100/160digit independent checks.
12. **Invariant**: Derived Fourier multiplier is nonzero with no poles in |Im w|<.5 for alpha>=.5; numerical recurrence and quasi-periodicity are cheap controls.
13. **Monotone**: Do not assume increasing alpha or shift size removes more nodes; compare entire configurations.
14. **Weaker bridge**: A validated single source zero refutes global logarithm for that representation; failed root starts cannot prove zero freedom.
15. **Stronger hunch**: Test whether source zeros recur in Floquet tails even when central scans appear empty. This is a candidate, not assumed.
16. **Minimal counterexample**: One independently validated interior source zero suffices against a proposed zero-free representation.
17. **Representation**: Use geometric shift resolvent and its bilateral exponentially weighted periodization; preserve boundary poles explicitly.
18. **Technique**: Cached deep/source-method searches and a recent resummation paper motivate checking cancellations across kernel and resummation; no physics theorem transfers.
19. **Fake proof**: A nonvanishing Fourier multiplier preserves spectral zeros but does not imply a zero-free source or an RH selector.
20. **Missing lemma**: A globally controlled zero-free positive source representation plus a valid source-to-spectrum theorem; neither follows from finite scans.
21. **Dependency**: Literal theta -> positive shift convolution -> exact geometric multiplier -> source-node witnesses; no connection to HB action is asserted.
22. **Nearby false**: Do not set new exponential tails to zero or call a positive source sufficient for RH.
23. **Boundary**: Use alpha>=.5 only; poles at Im w=+-alpha remain. Complex source strip is |Im z|<pi/4; node absence is never inferred from a finite search.
24. **Salvage**: If complex nodes persist, locate their tail structure and retain the zero-preserving representation as an exact candidate for a different analytic method.

## Frozen independent challenge
For all14 configurations, select the lowest-imaginary root actually found in each full/tail case; additionally challenge the actual full-source roots at tail translations8L and16L. These56 witnesses are tested at100/160digits (112 tasks), with recomputed theta/shift cutoffs, a wider shift window, independent Jacobi theta derivatives, local32-point numerical winding and residual/derivative estimates. Minimum-found is not globally nearest. Every case is preserved, including failures. Independent evaluator reflects to Re z>=0 using previously checked literal-source symmetry, then uses Jacobi derivatives; no original explicit n-series is used in that value evaluation. This tests numerical persistence only; no interval/Rouche certificate, global zero census or infinite-tail theorem is claimed.
