# EDQ weighted fifth circulation and zero landing

Stage: 3-formalized; dependency-closed paper proof and Lean verified.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
RH status: no sign or zero-location conclusion.

For arbitrary complex increments a_n,b_n, form the literal product of the six-coordinate
matrices `chainExp(a_n,b_n)`. Let x_N=sum_(n<N)a_n, y_N=sum_(n<N)b_n and let U_N,V_N,W_N
be its entries (0,3),(0,4),(0,5). The first three entries of its zeroth row are
1,x_N,x_N^2/2. On one straight segment, x=x_N+t*a_N and y=y_N+t*b_N.

The polynomial circulation on that segment is the actual complex integral
`J_N=integral_(0..1) x*y^3*a_N dt`. Its exact value is

`a*x*y^3 + (a^2*y^3+3*a*x*y^2*b)/2 + (3*a^2*y^2*b+3*a*x*y*b^2)/3`
`+ (3*a^2*y*b^2+a*x*b^3)/4 + a^2*b^3/5`.

Multiplication by the actual chain exponential gives the same increment for

`Q_N = -6*W_N + 6*y_N*V_N - 3*y_N^2*U_N + x_N^2*y_N^3/2`.

Since Q_0=0, telescoping proves sum_(n<N)J_n=Q_N at every finite cutoff, with every terminal
term retained. This is symbolic polynomial algebra, not a numerical experiment.

Specialize a_n and b_n to the actual moduli-two and moduli-three deletion jumps with weights
(n+1)^(-s). The source-product identity identifies these matrices with the already constructed
chronological product. For Re(s)>1/5 it converges. At any such zeta zero s!=1, the corpus's
level-one zero landing gives x_N,y_N→0; all terminal terms vanish by matrix convergence.
Thus the fifth word equals `-(sum J_n)/6` in the limit.

There is also absolute source control at those zeros. With sigma=Re(s), r_n=(n+1)^(-sigma),
existing Abel bounds give |x_n|<=A_1*r_n, |y_n|<=A_2*r_n, |a_n|<=r_n, |b_n|<=2*r_n.
For 0<=t<=1 the segment integrand therefore has norm at most
`(A_1+1)*(A_2+2)^3*r_n^5`. Its integrals form an absolutely summable series when 5*sigma>1.
No positivity is inferred from the complex fifth word or from the unweighted polygon moment.

Corpus sources inspected: EulerDeletionJointNilpotentWitness, EulerDeletionJointProductOneFifth,
EulerDeletionJointFifthPhase, EulerDeletionJointPolygonMoment, EulerDeletionMixedWordBoundary,
EulerDeletionQuasiShuffleZeroLanding, and EulerDeletionQuasiShuffleSecondConvergence.
The required independent signed arithmetic comparison remains open.

## Absolute convergence as an exact zero test

The actual integral factors as `J_n=a_n*R(x_n,y_n,a_n,b_n)`, where R is the degree-four
polynomial obtained by removing the common factor a from the displayed segment formula.
If endpoints tend to X,Y and increments tend to zero, R tends to X*Y^3. For modulus two,
`|a_n|=(n+1)^(-sigma)` exactly. Hence if X*Y^3 is nonzero, the norm of J_n is eventually
bounded below by a positive constant times `(n+1)^(-sigma)`, and its absolute series diverges
when sigma<=1. In the open strip `1/5<sigma<1`, each deletion endpoint is
`(1-p^(1-s))*zeta(s)`, with both p=2 and p=3 factors nonzero by their norms. Therefore the
actual circulation is absolutely summable exactly at zeta zeros in that strip. The forward
implication is a source convergence criterion; it does not determine the zeros' real parts.


## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionWeightedFifthCirculation.lean`
(400 lines; 19 public theorems, six public definitions, four private lemmas and one private
linear coordinate readout). Namespace: `RHTower.DeletionJointCirculation`.

- `segment_eq`, `prefix_first_coordinates`, `finite_circulation_eq_boundary`: actual complex segment integral and complete finite endpoint identity.
- `source_factor_eq_chainExp`, `source_product_eq_pathProduct`: exact arithmetic source identification at every cutoff, including incomplete six-blocks.
- `circulation_limit_of_closed_endpoints`: limiting identity with all terminal products accounted for.
- `norm_segment_le`, `norm_sourceSegment_le_at_zero`, `sourceSegment_summable_at_zero`: full fifth-power bound and absolute convergence at zeros.
- `source_fifth_word_at_zero`: actual unit-product limit, absolute circulation, and exact fifth-word value.
- `segment_eq_mul_response`, `segmentResponse_tendsto`, `norm_two_jump`: literal increment factorization, endpoint multiplier, and exact modulus-two jump norm.
- `source_endpoint_tendsto`, `source_response_tendsto`, `endpoint_product_eq_zero_of_summable`: nonzero endpoints force a nonsummable first-power tail below exponent one.
- `source_endpoint_value`, `one_sub_dilation_ne_zero`, `sourceSegment_summable_iff_zero`: full endpoint value, nonvanishing elementary factors, and exact source zero test on `1/5<Re(s)<1`.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_circulation.lean`, exit 0, no diagnostics.
Final leaf audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionWeightedFifthCirculation`, exit 0. Only the new leaf rebuilt (5.1 seconds); dependencies cached. Umbrella import appended; no full or umbrella build.
New-only axiom audit: `lake env lean /tmp/edq_circulation_axioms.lean`, exit 0. All 25 new public declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Private lemmas are covered by their dependency closure. No added axioms, admissions, numerical premises, or external computation certificates.

Repository `scripts/formal_tools.py lint` ran once and passed, with existing file-size warnings.
The index was refreshed once. Scoped whitespace and wiring checks passed. Both owned scratch
Lean sources were removed; all owned Lean/build/axiom/lint/index handles finished. Logs remain
in `/tmp/edq_circulation.api.log`, `.check.log`, `.build.log`, `.axioms.log`, `.lint.log`, and
`.index.log`.

RH remains unproved and unfalsified. The absolute-convergence criterion detects zeros; it does
not exclude their possible off-line locations. No route is retired by this certificate.
