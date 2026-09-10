# EDQ prime-count endpoint variance — 2026-09-10

RH goal remains ACTIVE and unproved. Frontier map is READ ONLY. No numerical experiment was run.

New closed leaf: formal/GaloisForLFunctions/RHTower/EulerDeletionPrimeCountEndpointVariance.lean, namespace RHTower.PrimeCountDamping. Imports EulerDeletionPrimeCountAmplification and Sieve.DivisorSwap. Umbrella import wired immediately after amplification. 13 public theorems, successful scratch plus new-only axiom audit; all use only propext, Classical.choice, Quot.sound. Final leaf-only lake build --old GaloisForLFunctions.RHTower.EulerDeletionPrimeCountEndpointVariance passed, only this leaf compiled (133s, 13,642 cached/dependency jobs). Index refreshed (4 changed, 3 foreign); formal lint and own-scope diff check passed. No umbrella/full build. All own processes terminal. Eight owned temp files deleted. No commits, frontier edit, or STATUS edit. STATUS already distinguishes energy shape from minimum value.

Definitions:
jetCoeff n = (mu n : R) * n.primeFactors.card.
endpointJet N = sum_(1<=n<=N) (jetCoeff n : C) • bdGen(1/n).
jetHarmonic N = sum jetCoeff(n)/n.
primePowerCount k = sum_(1<=n<=k) if IsPrimePow n then 1 else 0.
jetCell N k = sum jetCoeff(n)*(k mod n)/n.
A_N = sum_(1<=k<=N) k/(k+1).
B_N = sum Q(k)/(k+1).
C_N = sum Q(k)^2/[k(k+1)].
jetVariance N = C_N - B_N^2/A_N.

New theorems:
sum_divisors_damped: sum_(d|n) mu(d)u^omega(d)=(1-u)^omega(n), n nonzero, all real u.
sum_divisors_jet: sum_(d|n) mu(d)omega(d)=-1_(n is prime power), n nonzero.
jet_floor_sum: sum_(n<=k) jetCoeff n*floor(k/n)=-Q(k).
jetCell_eq: k<=N -> jetCell N k=k*jetHarmonic N+Q(k).
hasDerivAt_source_one: literal carrier derivative H_N'(1)=endpointJet N.
hasSum_endpointJet_energy: full infinite discrete cell-square series sums to actual ||J_N||^2.
endpointJet_prefix_lower: sum_(k<=N)(k*h_N+Q(k))^2/[k(k+1)] <= ||J_N||^2.
jet_prefix_square_completion: prefix(h)=V_N+A_N*(h+B_N/A_N)^2 for N>=1.
jetVariance_le_endpointJet_energy: unconditional V_N <= ||J_N||^2, all N (line230).
jetVariance_eq_minimum: V_N equals prefix at h=-B_N/A_N.
jetVariance_nonneg.
jetVariance_monotone.
jetVariance_pairwise (line278):
2*A_N*V_N = sum_i<=N sum_j<=N (i*Q(j)-j*Q(i))^2/[i(i+1)j(j+1)].

Main paper attack in docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md, section 'Prime-count endpoint: prime-power forcing and spatial variance' starts line1917. Asymptotic and curvature results below are PAPER ONLY, NOT Lean:
1. Using PNT alone on windows N^alpha and N gives ||J_N||^2 >= c_alpha*N^alpha/log(N)^2 for every fixed 0<alpha<1.
2. Current source-verified corpus theorem Sieve.primeCounting_sub_logIntegral_isBigO (formal/.../Sieve/PrimeCountingBigO.lean:56) gives pi(x)=li(x)+O(x exp(-c sqrt(log x))). Two integrations by parts and O(sqrt(x)log x) proper-prime-power count imply Q(x)/x=1/log x+1/log^2 x+O(log^-3 x).
3. Comparing proportional windows [N/4,N/3] and [2N/3,N] gives ||J_N||^2 >= c*N/log^4 N.
4. Sharp finite-invariant limit: V_N*log^4(N)/N -> 1. Put L=log N, t_k=k/N, w_k=k/(k+1), r_k=L^2*(Q(k)/k-1/L). On k>=N exp(-sqrt L), r_k=1-log(t_k)+O((1+log^2(t_k))/L). Omitted head contributes O(exp(-sqrt L)*L^4) to normalized r-square mass. Integral comparison gives normalized first/second log moments 1,2, bounded fourth moment. Weights w_k can be replaced by1 with vanishing error using same split. Thus A/N->1, weighted mean r->2, weighted mean square r->5, and normalized variance ->5-4=1.
5. K_N=H_N''(1) has norm O(sqrt N log^2 N) from omega(n)<=log N/log2 and sum generator norms <=4sqrt N. Existing raw-source every-log saving implies ||H_N(1)|| ||K_N||=o(N/log^4 N). Therefore energy second derivative at1 equals 2||J_N||^2+2Re<H_N(1),K_N>=(2+o(1))||J_N||^2>0 eventually. This is actual full-energy local convexity, NOT an energy-height bound or sign of first derivative.

Next meaningful work: close the explicit prime-power variance asymptotic / forcing-curvature result in Lean, and seek control of signed <H,J> that yields the actual cofinal subpower ceiling. Do not mistake large derivative norm or local convexity for RH. Scalar optimization is sharp only for the finite prefix; it does not permit arbitrary full-tail counterterms.

Other exact ideas tested:
mu(n)*(1-t)^omega(n)=(mu * t^omega)(n). Dilation expansion transports smaller cutoffs but positive norm majorant retains sum_p<=N t/sqrt p, growing at fixed t. Higher factorial divisor jets have exact omega=k support; no bound uniform in order/cutoff obtained. Finite degree alone or averaging phases does not bound actual arithmetic endpoint.

Five broad deep/method searches (OR --any,180s,max2rounds,cached) inspected all declaration/candidate/source lanes. All partial. Four snapshots pending; one resolved inventory 56,124files,46,699Lean, considerable pending/stale compiler status. Current hashes verified for PrimeCountingBigO and squarefree Sieve.TruncatedMoebius.sum_divisors_moebius_filter_card_le; latter cannot apply to arbitrary n. No ready asymptotic producer found. Fifth query found HTGeometry/BoundedVariationRiemannSum.lean:49 norm_rightEndpoint_riemannSum_sub_integral_le_eVariationOn (not yet read/applied); scalar MertensSecondSharp.invLogVar telescopes and ordinary covariance formulas, no source identification.

Recent broad arXiv intake: newest-first avalanche and screening. Janssens/Moll/Schindler 2609.08666v1 (8Sept2026) AppendixA/B: positive normalized weights and iid equal-variance cluster times, time ordering correlations omitted in analytical proof; no EDQ covariance transfer. Huang/Breizman2609.08051v1 (7Sept2026): marginal-stability closure, 1D spectral ridge assumed, finite cap regularization; no proved arithmetic dissipation. Relevant sections read, links and premise audits in card. No external result imported.

Lean lessons:
- ArithmeticFunction.IsMultiplicative.multiplicative_factorization takes explicit function then proof: method form (hz.mul hf).multiplicative_factorization _ hn, NOT ... n hn.
- sum_range_succ ambiguous due global real telescope; qualify Finset.sum_range_succ.
- HasDerivAt function/scalar-module instance defeq can need convert! h using1. This solved source carrier cast and scalar power derivatives; no extra axioms.
- RCLike.real_smul_eq_coe_smul (K:=C) converts real smul to complex coercion.
- hasSum_sum handles finite sums; HasSum.sum is a different theorem.
- Parenthesize HasSum target (||J||^2), else parser powers the proposition.
- Distribute sums divided by scalar with sum_div, not its reverse.
- For rational Gram term ring normalization first simp only [div_eq_mul_inv,mul_inv_rev].
- Nat.sum_Icc_eq_sum_range does not exist here; use sum_bij j->j+1.
- field_simp sometimes closes pure rational identity; omit trailing ring then.
