# Positive theta-source representation — report

112 saved tasks; 112 passed their implemented checks, 0 recorded failures. Whole-family wall time 2.129s. Original downloaded checksums verified. Exact environment, executable code, frozen parameters, source provenance and raw failed starts are retained.

## Question and mathematical objects

Can a positive source representation preserve the RH-strip spectral zeros while avoiding the literal source's complex zeros? Let L=log(p),r=p^(-alpha), and Psi(z)=sum_{k in Z}r^|k|Phi_R(z+kL), alpha>=1/2. Geometric summation yields Fourier multiplier (1-r^2)/(1-2r*cos(wL)+r^2), with no zeros and poles only at2pi*n/L+-i*alpha. The zero set in the strict RH strip |Im w|<1/2 is therefore preserved by this derived transform relation, subject to its analytic justification; it is not a newly audited Lean theorem. New exponential tails and boundary poles are retained.

The rescaled right tail is H(z)=sum_{j in Z}r^(-j)Phi_R(z+jL), satisfying H(z+L)=rH(z). Thus exp(alpha*z)H(z) is periodic. Test both the full source and one tail cell, then the full source at translated tail-node positions8L and16L. The latter are actual finite-coordinate calculations, not a proof of infinitely many zeros. All computations use precision-dependent theta/shift sums; no old short Fourier window is reused for the exponential tails.

## Outcome

All14 configurations p=2,3,5,7,4,6,2.5 and alpha=.5,1 have selected complex zeros in both full source and tail. For each configuration, the lowest-imaginary node found in each search and the two far-tail full-source roots passed100/160digits with independent Jacobi evaluation, enlarged shift cutoff, numerical winding1 and residual/derivative checks. This is56 selected witnesses,112 precision tasks. Worst inferred root errors are1.63e-100 and2.65e-160 respectively. All successful winding values are1. These are numerical diagnostics, not rigorous error enclosures.

| Shift base p | alpha | Lowest imaginary part found in tail (not global minimum) |
|---|---:|---:|
| 2 | .5 | 0.221553994964 |
| 2 | 1 | 0.21987146999 |
| 2.5 | .5 | 0.149151809016 |
| 2.5 | 1 | 0.148486821395 |
| 3 | .5 | 0.113582684711 |
| 3 | 1 | 0.113208016598 |
| 4 | .5 | 0.0774650480104 |
| 4 | 1 | 0.0772955908884 |
| 5 | .5 | 0.0589482621353 |
| 5 | 1 | 0.0588529129131 |
| 6 | .5 | 0.0476237554395 |
| 6 | 1 | 0.0475634351387 |
| 7 | .5 | 0.0399665845503 |
| 7 | 1 | 0.0399254419664 |

For p=2,alpha=.5, a tail node is .373859475678791+.221553994963502i; full-source nodes near5.919036920158354+.221553994963502i and11.464214364637916+.221553994963502i survive independent checks. For p=7,alpha=.5, a tail node has imaginary part .039966584550298. Composite and noninteger bases also retain nodes. The kernel need not regularize complex-source geometry even though it preserves the RH-strip spectral zeros.

## Whole-landscape interpretation and positive salvage

Each tested geometric-dressing candidate fails to admit a holomorphic logarithm throughout the source strip |Im z|<pi/4, numerically witnessed by interior zeros. This kills this specific attempt to remove the logarithm obstruction without moving the zeta spectrum; it does not kill source representations in general or HB. The useful positive survivor is the explicit link between a zero-preserving spectral multiplier and a periodic source tail. It makes source geometry a representation-dependent quantity that an RH criterion must control, rather than treating its improvement as automatic.

No prime-specific distinction appears in these finite witnesses; this is not a theorem that arithmetic never matters. The next discriminating candidate is a continuous Green-kernel representation without discrete periodic tails. A naive Gaussian-source smoothing scan was rejected after deriving its direct correspondence to a backward de Bruijn deformation; merely replotting it would not be a new question. The two competing issues remain separate: source-logarithm feasibility and a theorem that turns source structure into spectral real-rootedness.

## Scope

These numerical observations are not interval certificates, new Lean proofs, a complete zero census or RH counterexamples. No claim of historical priority is established. Counts are roots found by declared starts; failed searches never prove absence. Polynomial-modified sources change arithmetic functions. Source-node cancellation uses high-precision numerical coordinates. SS/SV/VV actions, physical remainders, onset/contact and boundary work are outside these arithmetic calculations, not omitted zero terms. No HB identification or extinction claim follows. No Lean builds were run.
