# Candidate positive survivor: torus density of exact integer-null mixtures

Status: finite Gram-packet realization and normalized realization from actual representing measures have passed direct Lean compilation and targeted leaf builds. The larger measure-level density construction and Jensen transfer remain unformalized. Scientific novelty is unestablished. This is not a PBAP proof; do not promote the full construction to formalized status.

## Precise proposed theorem

Let T be the countable product of unit circles indexed by primes, and let `iota(t)=(exp(i t log p))_p`. Let M be the probability measures on T whose nonconstant holomorphic monomial moments vanish. Then M is the weak closure of the pushforwards under iota of normalized spectral densities

    H(t) dt/(2 pi),    H(t) = sum_j |Fourier(f_j)(t)|^2,

where the sum is finite, every f_j is smooth and compactly supported, and the aggregate autocorrelation vanishes at every nonzero signed integer logarithm. Coefficients can be absorbed into the f_j. In the conjugation-invariant part of M, H can be chosen even.

The stronger complex autocorrelation-null property here implies the symmetric real constraints of WP01. Conversely, for the exact WP01 class one first symmetrizes H, which preserves its energy against the even full functional. Thus the conjugation-invariant version is the directly relevant statement.

No uniform bound on archimedean energy, support diameter, or spectral location is asserted. This omission is essential, not a hidden positivity premise.

## Construction using finite Fejer sums

Fix a finite prime set S, and a representing probability measure mu on its torus. Convolve mu with the product Fejer kernel of order K. The resulting nonnegative trigonometric polynomial w has mean one and has no nonzero Fourier coefficient in the positive or negative orthant. It converges weakly to mu as K increases. Write

    w(z) = integral |sum_{0 <= alpha_p <= K} z^alpha conjugate(y^alpha)|^2
                    dmu(y) / (K+1)^|S|.

The finite moment matrix in this expression is positive semidefinite. Factor it as a finite Gram matrix to obtain

    w(z) = sum_j |P_j(z)|^2

with ordinary holomorphic polynomials P_j. This particular sum-of-squares representation follows from the displayed Gram integral; it does not invoke a general multivariable Fejer–Riesz theorem.

Explicitly, for each integer multi-index gamma, the Fourier coefficient is

    w_gamma = mu_gamma product_{p in S} max(0, 1-|gamma_p|/(K+1)).

Indeed, for each coordinate there are `max(0,K+1-|gamma_p|)` pairs of box indices with difference gamma_p. This proves preservation of the zero monomial moments, normalization, and convergence of every character moment as K increases. Uniform approximation by trigonometric polynomials then proves weak convergence; no unquantified convergence property of an unfamiliar Fejer operator is needed.

Choose a real smooth bump beta_delta of L2 norm one, supported in an interval of length delta. Its autocorrelation C_delta has support in [−delta,delta] and C_delta(0)=1. Put

    H_delta(t) = |Fourier(beta_delta)(t)|^2 w(iota(t)).

Every monomial z^alpha becomes exp(i t log n_alpha), with n_alpha an integer. Therefore each `Fourier(beta_delta)(t) P_j(iota(t))` is the Fourier transform of a finite sum of translates of beta_delta. These are actual smooth compact tests, so H_delta is a finite Weil-test mixture without needing scalar convolution-root factorization.

Only finitely many frequencies lambda_gamma=sum_p gamma_p log p occur in w. Except for zero, each surviving gamma has both signs. Unique factorization implies exp(lambda_gamma) is neither an integer nor the reciprocal of an integer. Consequently every surviving frequency has positive distance from the locally finite set {±log n : n>=2}; for the zero frequency the distance is log 2. Choose delta below the minimum of these finitely many positive distances.

The aggregate autocorrelation is the finite sum

    C_mix(x) = sum_gamma w_gamma C_delta(x + lambda_gamma)

(reverse every lambda if the opposite Fourier convention is used). It vanishes exactly at all ±log n, not just at a selected cutoff. By also taking delta below every nonzero |lambda_gamma|, its value at zero is exactly one. Hence the spectral mixture is normalized.

For any fixed torus character z^alpha, integration against the pushed-forward spectral measure gives a finite sum of C_delta(lambda_alpha+lambda_gamma). As delta tends to zero, every nonzero argument is eventually outside the support, and the value becomes exactly the corresponding Fourier coefficient of w times Haar measure. Unique factorization rules out extra zero frequencies. Trigonometric polynomial approximation then gives weak convergence to w times Haar measure.

Finally take a diagonal limit in K and in finite prime sets. A representing measure on the full prime torus restricts to a representing measure on each finite torus; conversely extend a finite-torus target by Haar measure on the other primes. Finite-coordinate continuous functions are uniformly dense in C(T). These observations finish the weak-density construction. For conjugation-invariant mu, Fejer smoothing preserves conjugation symmetry; choosing beta_delta real makes H_delta even.

The reverse containment follows directly from the exact Fourier-null identities and weak continuity of the monomial moments.

## A concrete bidisc obstruction to the Jensen strengthening

The general distinction between representing and Jensen measures is classical. The following explicit bidisc construction is included to avoid importing the smooth strictly pseudoconvex theorem into a polydisc where its hypotheses do not apply.

Fix 0<a<1, put b=2a/(1+a^2), and let

    B(z) = (b-z)/(1-bz),
    p_a(z) = (1-a^2)/|z-a|^2,  |z|=1.

Then 0<b<1, B maps the unit circle to itself, and B(a)=a. Let m be normalized circle Haar measure. Define the diagonal measure mu_0 by z -> (z,z), the measure nu_2 by the same map with density p_a, and nu_1 by z -> (z,B(z)) with density p_a. The Poisson formula gives

    integral F dnu_1 = integral F dnu_2 = F(a,a)

for every holomorphic polynomial F. Both compositions are holomorphic on a neighborhood of the closed disc, since the pole of B lies outside it. Also mu_0 represents evaluation at (0,0).

Since p_a <= (1+a)/(1-a), choose 0<epsilon<(1-a)/(1+a). The measure

    mu = mu_0 + epsilon (nu_1 - nu_2)

is a positive probability measure representing (0,0). It is invariant under complex conjugation. Take

    P(z,w) = (1-bz)w - (b-z).

P vanishes on the graph of B and P(0,0)=−b is nonzero. On the diagonal, P(z,z)=2z-b(z^2+1), whose roots are a and 1/a, so it has no unit-circle zero. Thus the diagonal logarithm is bounded, while the graph component has positive mass and log|P|=−infinity. More robustly,

    integral log(|P|+eta) dmu -> -infinity  as eta decreases to zero.

For a sufficiently small fixed eta, this integral is strictly below log b. The integrand is continuous. The proposed density theorem therefore transfers the strict inequality to an actual normalized smooth integer-null **finite mixture**. Since log|P| <= log(|P|+eta), that mixture is not a Jensen measure either. Classical one-dimensional smooth scalarization would also yield a scalar example, but the mixture statement already concerns the exact WP01 cone and avoids that extra dependency.

## Meaning and limits

If the construction survives its audits, integer-null constraints impose no additional weakly closed torus-measure property beyond representing the origin. In particular, a universal Jensen inequality cannot supply PBAP. This does not negate PBAP: the Weil energy remembers the real frequency variable t, while the compact prime-torus topology forgets its size. The construction deliberately permits frequency mass to move to arbitrarily large heights.

The positive survivor is the exact finite Fourier-moment realization and then its weak-density consequence. `WeilWorkPBAPGramPackets` certifies the finite matrix realization, actual full-cone mixture, and exact mass formula below. `WeilWorkPBAPMomentPackets` constructs the actual representing-measure moment matrix and normalizes its smooth packet mixture to mass one. Neither proves weak convergence. The Jensen no-go remains open until that survivor is fully checked and formalized. `WeilWorkPBAPNullRepair` provides a separate finite-defect correction bridge.

## Available corpus interfaces and next checks

- `RHTower.weilTest_sum_translates` gives the finite translate autocorrelation expansion in `WeilPositivityMultiplicativeToeplitzBound.lean:459`; source checked.
- The same module already proves `RHTower.weilTest_translates_log` (line 668) and `RHTower.weilTest_translates_neg_log` (line 710): a common packet whose autocorrelation vanishes for `|Y| >= 1/(N+1)` selects precisely the divisibility diagonal. These are direct, checked starting points for the finite-mixture realization. Do not reprove their scalar expansion.
- `GaloisForLFunctions.primeTorus_kronecker_dense` exists and its source was checked, but the Fejer construction above avoids needing quantitative Kronecker approximation.
- Finite Gram factorization, torus characters, integral Gram positivity, and packet-mixture normalization interfaces are now verified. Fejer box counting, spectral probability normalization/pushforward, and weak-convergence interfaces still need their own `/tmp` Lean checks and connections.
- For a finite set of rational observations, integer log separation in the existing `log_gap` lemma should also isolate all rational-ratio frequencies after clearing denominators. A sufficiently narrow existing `narrowBump` can therefore avoid introducing a new analytic bump construction. The explicit Gram/counting formula above may avoid a general torus convolution API.
- Deep search for this mechanism completed with partial coverage (`semantic_retrieval` and `filter_and_judge` unfinished), output `/tmp/wp01-torus-density-search.json`. Candidates and source arguments were inspected; no closing realization theorem was found among them. Search results do not substitute for a novelty verdict. Classical ingredients alone are not new scientific knowledge.

## Exact finite realization: dependency-closed paper subtheorem

Fix natural numbers N and L. Index a positive semidefinite complex matrix A by the integers 1 through N. Let beta be the existing `narrowBumpC (N*L)`, let m be its positive squared L2 mass, and set x_j=log j−(log N)/2. Then there exist N smooth compactly supported complex tests f_i such that for every pair of positive integers a,b with b<=L,

    sum_i (f_i * tilde(f_i))(log a - log b)
      = m sum_{j,k=1}^N [a*k=b*j] A(j,k).

This statement holds for the zero matrix and for N=0 as well; empty sums are zero. The smoothness, support and exact matrix realization are conclusions, not supplied hypotheses. Positive semidefiniteness specifies the matrix domain.

Proof. Factor `A=B^* B`, and put c_i(j)=conjugate(B(i,j)). Then sum_i c_i(j) conjugate(c_i(k))=A(j,k). Set f_i(u)=sum_j c_i(j) beta(u−x_j). Finite translation and linear combination preserve smoothness and compact support. Expanding the autocorrelation and summing over i gives

    sum_{j,k} A(j,k) C_beta(log a-log b-x_j+x_k).

The argument of C_beta equals log(a*k)−log(b*j). If a*k=b*j it is zero and C_beta(0)=m. Otherwise both integers are positive and b*j<=N*L, so the existing integer log-gap theorem bounds its absolute value below by 1/(N*L+1). The bump radius is 1/(4(N*L+1)); its autocorrelation therefore vanishes outside radius 1/(2(N*L+1)), which is strictly smaller than the log gap. Every unwanted term vanishes. This proves the formula for every a at once; no finite numerator cutoff is introduced.

In particular, for L>=1, if every sum along a nontrivial multiplicative diagonal of A is zero, the resulting mixture is null at all positive integer logarithms; Hermitian symmetry gives all negative ones. At a=b=1 the mass is m times trace(A). If trace(A)>0, scalar normalization gives probability mass one. These consequences are algebraic uses of the displayed formula; no archimedean sign is obtained.

Audit verdict for this subtheorem: **BRIDGE**. It is a concrete harmonic-analysis realization using classical finite Gram factorization and the corpus's integer log separation. Its value is in certifying actual admissible tests for the proposed obstruction. The broader weak-density and Jensen no-go remain unfinished until their measure and normalization steps are formalized. External searches did not establish novelty; no scientific novelty claim is made for this subtheorem.

### Passage to the exact WP01 mixture interface

Given the realized family, define the finitely supported coefficient function by
`c = sum_i single(f_i, 1)`. Repeated tests have their coefficients added, so every coefficient is nonnegative. For any real observable F, `sum_f c_f F(f) = sum_i F(f_i)`. Hermitian symmetry gives `sum_i C_i(-log n) = conjugate(sum_i C_i(log n)) = 0`; taking the real part of the sum of these two identities and dividing by `sqrt n` gives exactly `sum_f c_f logValue(f,n)=0`. Every test occurring in c is smooth. This proves admissibility in the actual full PBAP cone, including aggregate cancellation, without assuming positivity of its energy.

### Representing-measure connection: closed paper theorem

Write `T = product_p Circle`, indexed by primes, and define `chi_n(z) = product_p z_p^(v_p(n))` for positive integers n. These are continuous unit-modulus functions, `chi_1=1` and `chi_(mn)=chi_m chi_n`, by finite prime factorization. Let mu be any probability measure on T representing the origin, in the precise sense `integral chi_n dmu=0` for every n>=2. For arbitrary complex coefficients d_1,...,d_N define

    A(j,k) = d_j conjugate(d_k) integral chi_j conjugate(chi_k) dmu.

This is the actual integral Gram matrix of the bounded continuous features `d_j chi_j`; hence it is positive semidefinite. All feature products are integrable since T is compact and mu is finite. If j=n*k with n>=2, its integral is `integral chi_n=0`, so **each** such matrix entry vanishes. Thus A belongs to the finite null-matrix class already realized in Lean. On the diagonal its value is `|d_j|^2`, so its trace is exactly `sum_j |d_j|^2`.

More generally, if a*k=b*j with a,b,j,k positive, multiplicativity and unit modulus give `chi_j conjugate(chi_k)=chi_a conjugate(chi_b)` pointwise. Put `M_mu(a,b)=integral chi_a conjugate(chi_b) dmu`. The verified finite packet theorem therefore gives smooth compact tests satisfying all integer-null constraints and, for every a>=1 and 1<=b<=L+1,

    sum_i C_i(log a-log b)
      = packetMass(N,L+1) M_mu(a,b)
        sum_{j,k=1}^N [a*k=b*j] d_j conjugate(d_k).

Their mass is `packetMass(N,L+1) sum_j |d_j|^2`. If d is nonzero, divide the nonnegative mixture weights by this positive mass. Its normalized rational samples are the target moment multiplied by the displayed finite correlation of d divided by `sum_j |d_j|^2`. For d equal to the normalized indicator of a prime-exponent box, that correlation is precisely the product Fejér multiplier. This last counting/convergence step is separate; the matrix connection above has no open analytic input.

Verdict: **BRIDGE**, extending the verified realization to actual representing measures. Positivity of the moment matrix is proved from integration, not supplied as a new assumption. This theorem still does not control the full Weil functional. Classical integral Gram theory and Fejér approximation are its parent mechanisms; scientific novelty is not claimed.

### Energy audit and reusable counting machinery

The refreshed corpus contains `WeilWorkExposingRayPacketCoercivity`: its logarithmic coercivity law uses the compact primitive of polar packets and a corresponding inverse-mass identity. Those conclusions do not automatically apply to the nonpolar bumps above. The finite realization still makes no full-energy claim.

`HTGeometry/BohrMultiFejerMultiplier.lean` already proves the coordinate fibre count and exact product Fejér multiplier. These are source-checked candidates for the remaining finite-prime approximation argument; their availability is not a proof that the measure-level density theorem has been formalized. The representing-measure matrix connection and packet normalization are now compiled. The relevant next obligations are the normalized prime-exponent-box coefficient profile, its exact multiplier, actual spectral probability pushforward, and convergence.

### A precise limit on strengthening the topology

Even approximation to Haar measure on the two-prime torus cannot keep a uniform bound on the normalized spectral logarithmic moment `integral log(2+|t|) d rho(t)`. This is a standard tightness obstruction, not a new sign theorem. A uniform bound B gives `rho(|t|>R) <= B/log(2+R)`, hence tightness. Any weakly convergent subsequence on the real line has probability limit rho, and the continuous prime-phase map carries that limit to the claimed torus limit. But Haar on the two-prime torus cannot be the pushforward of a real-line probability measure: the image of each bounded real interval is a smooth curve of Haar measure zero, and the full orbit is a countable union of these compact null sets. Thus logarithmic moments must be unbounded along every such Haar approximation.

This conclusion concerns a positive logarithmic frequency moment. It does **not** follow from an upper bound on the full Weil functional, because the pole term can be negative. Passing from a full-energy bound to tightness would require an additional proved estimate controlling that pole term. No such estimate is assumed here. Verdict for this observation: classical compactness applied to this setting; do not present it as novel PBAP progress or spend a separate formalization cycle on it before the substantive density and sign questions.

### Exact spectral probability and remaining box argument

The next measure construction can use the corpus's literal C² Weil-test Fourier inversion, without a new Schwartz conversion. `RHTower.WeilRegular.pairTransform_ofReal` identifies the transform with `|paperFT f(-2*pi*xi)|^2`; `RHTower.WeilRegular.weilTest_eq_integral` reconstructs the autocorrelation by integrating this density against `exp(2*pi*i*xi*y)`. Its required support bound follows from compact support. The source proof also supplies an integrable decay majorant via `exists_norm_pairTransform_le`. These interfaces are source-checked, not yet verified in a new scratch import.

For a normalized nonnegative finite mixture c, set

    D_c(xi) = sum_f c_f |paperFT f(-2*pi*xi)|^2.

This is a continuous nonnegative integrable density. Fourier inversion at zero and `mixtureSample(c,0)=1` give `integral D_c=1`. Thus `rho_c = D_c dxi` is an actual probability measure. Push it forward by the existing prime phase map `clockPhasePoint (p -> log p) (2*pi*xi)`. The corpus's character evaluation and prime-log factorization identity give exactly

    integral chi_a conjugate(chi_b) d(pushforward rho_c)
      = mixtureSample(c, log a-log b).

No hypothetical Weil-positive producer or its spectral measure is needed. In particular, do not substitute `weilFullFunctional_weilTest_eq_lintegral`, whose `WeilPositiveFull` input would be circular here.

For the coefficient construction fix finite primes S and an integer K. Let B be the finite integers with prime exponents in `[0,K]^S`, and choose N at least their maximum. Put `d_j=|B|^(-1/2)` on B and zero elsewhere in `1..N`. Unique factorization makes the exponent parametrization injective; `|B|=(K+1)^|S|`, so this is a unit profile. For positive a,b with their prime factors in S, put `v_p=v_p(a)-v_p(b)`. The equation `a*k=b*j` says that the two box vectors differ by v. Each coordinate has exactly `max(K+1-|v_p|,0)` pairs. Hence, once K bounds every `|v_p|`,

    packetCoeffCorrelation(d,a,b)
      = product_{p in S} (1 - |v_p|/(K+1)).

Each factor lies in `[0,1]`. Telescoping the product gives the explicit error bound `0 <= 1-product <= sum_p |v_p|/(K+1)`. Thus the normalized realized measure's moment tends to the target moment; the target moment has modulus at most one by integration of a unit character. Let S exhaust the primes and let both K and the denominator resolution tend to infinity. Every fixed positive rational observation is then covered. Every finitely supported integer character is `chi_a conjugate(chi_b)` using the positive and negative exponent parts (`positivePart`, `negativePart`, `primeProduct`). The existing `span_torusCharacter_closure_eq_top`, plus the probability bound on integration, extends convergence to every continuous function on the compact prime torus. This is the complete paper argument; these remaining connections and the limit are still unformalized.

The direct energy attack remains separate. L353 already records mean-value positivity for sufficiently narrow packets on divisibility antichains. The present representing-measure moment matrices allow mixed fibres beyond that support class, but no new energy lower bound has been proved. A proposed sign theorem for them must retain the signed rank-two pole contribution and establish its comparison with the actual gamma term; positivity of the moment Gram matrix alone does not give that comparison.
