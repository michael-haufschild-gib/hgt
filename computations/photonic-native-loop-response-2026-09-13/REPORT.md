# Physical evolution and code monitoring define different loop responses

Numerical identification experiment, not a zeta-zero computation or a new Lean proof. No Riemann data enter the optical drive or code.

## Native physical cycle and the question

Use a canonical transverse oscillator qdot=p/epsilon(t), pdot=-q. For integer m>2, lambda=(m+sqrt(m^2-4))/2, let epsilon=1 for physical time pi/2, then epsilon=lambda^2 for physical time lambda*pi/2. Exact temporal matching gives F(T)=-diag(lambda^-1,lambda). The matrix g=[[lambda^-1,-1],[lambda,-1]]/sqrt(lambda-lambda^-1) has determinant1 and satisfies F(T)g=-gA for the integral matrix A=[[m,-1],[1,0]]. Thus the actual temporal cycle closes an optical displacement lattice. The intra-period path is retained; it need not itself be a geodesic.

For dimension d=2 or3, prepare finite-energy GKP code columns Psi_i=E_delta U(F_i g)comb, E_delta=exp(-delta*(q^2+p^2)/2). The comb columns are sum_n exp(2*pi*i*b*n)delta(q-sqrt(2*pi*d)*(n+(j+a)/d)), j=0,...,d-1. Use invariant stabilizer phases a=b=0 for d2 and a=b=.5 for d3. Let G_i=Psi_i^*Psi_i and W_i=Psi_i G_i^-1/2; every logical channel is retained. The endpoint overlap J=W_0^*W_final is the ideal lattice relabeling in these encoding coordinates.

Compare three complete operators: free physical evolution with a final code projection; products of moving code projectors alone; and physical evolution interleaved with those projectors. The interleaved step contains U(F_(i+1)F_i^-1)E_delta U(F_i g), not E_delta U(F_(i+1)g). Projective measurements and postselection are explicit additions to the dielectric model, with rejected probability recorded. Their microscopic implementation is not supplied.

The frozen question was whether combining physical transport and moving monitoring preserves ideal projective logical transport. Predictable effects such as finite-step measurement loss and the noncommutation of a squeeze with a fixed envelope were controls, not discovery targets. The unknown was the complete combined logical response.

## Findings

All20 initial configurations completed. Three complete64-step paths were checked independently at50/100/160digits using infinite inner Jacobi sums, twice the outer truncation and arbitrary-precision physical matrices, Gram inverse roots, chronological products and complex SVD. All9 independent tasks passed. The largest scaled100/160 full-map/scalar difference was5.12e-77; production comparison was below2.50e-8. These are numerical agreement measures, not interval error bounds or certified digits.

An earlier128-step50digit pilot also passed numerically but exceeded its75s sizing gate; the other8planned tasks did not run. The validation was reformulated as64-step complete paths. A step-refinement attempt stopped before physical computation because a job-parameter nesting bug caused KeyError(dim); the repaired16-case family completed. Both unsuccessful attempts are retained and are not counted as scientific successes.

For K, report mean survival Tr(K^*K)/d and the distance sqrt(2-2abs(Tr(J^*polar(K)))/d). The latter discards a common phase but detects changes in logical action. Raw K, all singular values and polar matrices are saved; renormalization does not hide rejection.

| d | m | delta | Steps | Geometric survival | Driven survival | Driven projective distance |
|---|---:|---:|---:|---:|---:|---:|
|2|3|.2|64|0.1340580307|0.9081594384|0.06380066409|
|2|3|.05|64|9.738705834e-11|0.9083192736|0.0007757147489|
|3|6|.2|64|0.001780180382|0.544962942|0.1653901782|

The d2,m3 comparison is a qualitative mechanism change: reducing delta from.2 to.05 makes the geometric reader nearly reject the whole state, while the driven reader keeps approximately91%survival. At the same time, high survival does not imply the exact ideal logical map.

Four configurations were refined through256,512,1024,2048steps in complex128. The table gives the last step count; the preceding point is retained to show the remaining resolution change.

| d | m | delta | Driven survival at2048 | Projective distance at1024 | At2048 |
|---|---:|---:|---:|---:|---:|
|2|3|.2|0.9969805248|0.06374677744|0.06374661857|
|2|3|.05|0.9969926206|0.0007762191399|0.0007762206141|
|3|6|.2|0.9806497564|0.1632056607|0.1631992141|
|2|10|.1|0.9445031017|0.04763902249|0.04763457333|

These data support a nonzero finite-energy logical mismatch that is not removed by simply increasing monitoring frequency. They do not prove an infinite-monitoring limit. The m10refinement is a numerical extension without its own full arbitrary-precision path validation; the validated structural examples are the m3/d2 and m6/d3 configurations above.

## Positive residue and whole-route meaning

The metric failure did not kill native dynamics. In this experiment the actual pump largely cancels the costly motion that pure geometric monitoring imposes on a sharp code state. A post-result dense-lattice Gaussian candidate predicts driven survival [1+(m^2-4)sin^2(pi/n)/4]^(-n/2) for n total steps. Existing delta=.05data agree approximately across d2/3 and m3/6. The determinant calculation is elementary; deriving this as a uniform code limit, particularly into a cusp, remains open. More agreement with that already-visible scalar estimate is not admitted as a new discovery experiment.

The surviving physical object is the combined transport/measurement operator over the lattice space. High probability of returning to a code is insufficient to identify its scalar automorphic response: a residual logical rotation or state-dependent attenuation can change the operator. Conversely, the large improvement over geometric monitoring is evidence that a physical realization should retain the actual drive rather than infer dynamics from distinguishability alone.

The ideal G/Gamma lattice action is conjugate to sampled modular geodesic flow; an isotropic angular ensemble of native squeezes has the hyperbolic Laplacian as its local scalar diffusion generator. Those derived bridges do not establish that the present finite-energy optical reader realizes the scalar modular cusp response. That requires handling its full logical/phase cocycle, finite-energy envelope, cusp boundary, physical ensemble and primitive incoming/outgoing normalization. On the standard scalar modular receiver, Riemann zeros rho map to resonances u=rho/2, so RH requires Re(u)=1/4, distinct from the unitary axis Re(u)=1/2. No confinement law follows from the present returns, survival or unitarity.

## Limits and reproducibility

The dielectric is an explicitly ideal lossless nondispersive two-layer model. Pump work is included by the actual nonorthogonal symplectic evolution, but material dispersion, bandwidth, pump backreaction and microscopic code measurements are unmodeled. No full HB action or extinction claim is made. No optical zeta spectrum was measured, and no RH zero was supplied as input. Logical finite-dimensional returns are not the spectrum of the full automorphic space.

Full code, frozen parameters, all24method operations, every raw map and Gram spectrum, independent evaluations and original download checksums are retained. Search provenance is cached deep/method search with partial pending coverage; inspected corpus gauge/connection statements do not identify this continuum optical response. Primary frameworks are PTC symplectic dynamics(arXiv2511.17317), GKP lattice/phase bundles(arXiv2407.03270,2410.07332), finite-energy encoding(arXiv2605.28784), and continuous-measurement holonomy(arXiv2608.11369). No published finite-energy gate formula was used as a numerical oracle. No Lean builds, new unconditional formal theorem, historical priority or journal-readiness claim.
