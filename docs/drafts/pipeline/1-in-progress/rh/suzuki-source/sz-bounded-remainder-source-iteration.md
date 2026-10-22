# Actual Suzuki source control by bounded-remainder iteration

- **ID:** sz-bounded-remainder-source-iteration
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** docs/reports/rh-current-frontier-map.md, route SZ
- **Statement:** Uniform actual odd covariance energy, actual Neumann Gamma admission, and matched physical mass O(a*exp(-a)) are Lean-closed. Next: growing physical coercivity and rescaled approximation error toward signed metric cancellation.

## Goal and status

The selected uniform odd-source estimate is now Lean-closed by
`exists_suzukiTaCoalescingOddEnergy_half_uniform_bound`; both final leaf
audits passed. See `../../../3-formalized/sz-matched-odd-source-bound.md`.
The subsequent Gamma admission and physical-response decay conjecture is
also Lean-closed; see `../../../3-formalized/sz-matched-odd-physical-decay.md`.
Continue with `sz-growing-physical-coercivity.md`. The complete original-cutoff signed Wronskian, canonical V2
normalization, shift removal, Xi identification and RH remain open.
No regularity or cancellation premise is to be added to the actual source
or response in the next theorem.

## Source contracts

- CCMRestrictedWeilPolarFreeShift: absolute scalar-minus-prime quadratic
  is bounded by the norm of the actual full bounded remainder.
- CCMRestrictedWeilPolarShiftLower: norm(B_a)>=sinh(a)+a, and the actual
  interval shift c_a satisfies exp(a)<=2*c_a. Direct leaf audit passed.
- CCMRestrictedWeilGroundFrequencyLocalization: norm of the finite-prime
  operator is at most 42*exp(a), through the literal positive coefficient sum.
- Sieve/VonMangoldtTwistScaledWidth: free-width estimate for the complete
  twisted Mangoldt prefix, including prime powers.
- Sieve/MenonHarmonicFullFrequencySchedule: a uniform relative majorant
  tends to zero, throughout a polynomially large frequency window and
  a growing cutoff window. No unweighted-prime or log-ratio phase
  substitution is permitted.
- Sieve/ChebyshevSharpSelfRateOne: the actual Chebyshev remainder is bounded
  by C*y*exp(-sqrt(log y)/960000), eventually.
- The existing actual Suzuki form and source welds give
  q(v)=Re<p,Jv>, q(v)>=Re<A Jv,Jv>, and q(v)>=norm(Jv)^2,
  with A=c_a I+B_a and p(x)=sinh(x/2) on [-a,a].

## Paper argument

Write M=exp(a), I=[-a,a], B=kI+P-T, c=c_a and H=B/c. Physical and
interval coordinates are related by their existing unitary. In particular
norm(B)<=c-1 and A=cI+B>=I. The form has an additional nonnegative Gamma
form norm. Neither Gamma's operator nor the Riesz response is iterated.

### 1. The shift lower bound

Let h_+=1_I exp(x/2), h_-=1_I exp(-x/2), f=h_++h_- and d=sinh(a)+a.
The exact pole Gram entries give norm(f)^2=4d and <Pf,f>=8d^2.
The ordinary B bound and the phase-recurrence bound for B-P give
8d^2<=2*norm(B)*4d. Since d>0, norm(B)>=d. Therefore
exp(a)<=2*(norm(B)+1)<=2c. This uses no prime asymptotic.

### 2. Uniform cancellation on any fixed exponential frequency window

Before compression, B is convolution by the finite signed measure

 k delta_0 + 1_{[-2a,2a]}(h)*2*cosh(h/2) dh
   - sum_{2<=n<=floor(exp(2a))} Lambda(n)/sqrt(n)
       *(delta_{log n}+delta_{-log n}).

For each fixed K>0, its Fourier multiplier satisfies

 sup_{|xi|<=exp(K*a)} |Bhat_a(xi)| / exp(a) -> 0.              (C)

Here is the complete proposed transfer. Put ambient X=exp(K'*a), with
fixed K'>K absorbing the Fourier convention and constants. The corpus
full-frequency majorant has lower frequency (log X)^311 and upper
frequency 2*pi*X. For all large a, every integer prefix between
exp(a)/2 and exp(2a) lies above exp((log X)^(19/20)), and its logarithm
is below log 2+(log X)^2. Consequently the complete twisted Mangoldt
prefix is o(y), uniformly in that whole prefix/frequency rectangle.
This precise prefix consequence is the new
Sieve/VonMangoldtTwistPolynomialWindow leaf; its direct leaf audit now passes.

Above the frequency floor, partial summation by n^(-1/2) gives o(exp(a))
for the weighted sum over exp(a)<n<=exp(2a). Its derivative has no frequency
factor: the prefix already contains n^(-i*tau). The smaller prefix has
absolute weight O(exp(a/2)). The matching continuous main term has norm
O(exp(a)/(1+|tau|)), hence is negligible uniformly in this high range.

Below the frequency floor, integrate by parts against psi(y)-y over
[exp(a),exp(2a)]. The derivative of y^(-1/2-i*tau) has norm at most
(1+|tau|)*y^(-3/2). The existing PNT error therefore bounds endpoints
and integral by C*(1+|tau|)*exp(a)*exp(-sqrt(a)/960000).
The frequency floor is a fixed power of a, so this is o(exp(a)); the
discarded head again costs O(exp(a/2)). The second polar exponential
has bounded integral, as does the fixed scalar atom. This proves (C)
on paper, retaining both prime powers and the continuous main term.

The signed measure's total variation is at most C_b*M, with C_b fixed:
its polar mass is 8*sinh(a)<=4*M and its prime mass is at most 42*M.
The scalar atom is fixed. Thus its convolution norm divided by c is
bounded by a fixed constant C_0>=2.

### 3. A class preserved by the actual bounded remainder

Represent functions by finite sums of atoms
  z*1_[l,r](x)*exp(s*x),  s in {1/2,-1/2}, [l,r] subset I.
Give a representation the budget
  V=sum |z|*exp(max(s*l,s*r)).
No infimum, completeness or BV representative is needed. Its sup norm
is at most V. Translations preserve the budget, and interval compression
decreases it. Each pole charge is at most
V*integral_I exp(+/-x/2)<=2*V*exp(a/2), so P has an output representation
with budget at most 4*M*V. The scalar and finite translations give the
remaining budget bound. After division by c, H maps a representation
of budget V to one of budget at most C_0*V, uniformly in aperture.

The elementary exponential integral gives, for xi!=0,
  |Fourier(f)(xi)|<=V/(pi*|xi|).
Consequently its L2 Fourier tail beyond R is at most C_f*V/sqrt(R),
with a fixed Fourier-convention constant C_f. Endpoint values are
irrelevant in L2. The odd source p has budget exp(a/2) and norm at most
exp(a/2). Thus f_j=H^j p has budget at most C_0^j*exp(a/2).

### 4. Many moments, with the aperture cutoff retained at every step

Fix eta=exp(-4), K=2*log(C_0)+10, R=exp(K*a), and n=ceil(a).
By (C) and c>=M/2, the normalized convolution multiplier is at most eta
on [-R,R], for all large a. Compression is contractive. Splitting each
f_j into its two Fourier parts gives

 d_{j+1}<=eta*d_j+C*C_0^j*exp(a/2)*R^(-1/2), d_j=norm(f_j).

Solving this finite scalar recurrence gives
 d_j<=eta^j*norm(p)+C'*C_0^j*exp(a/2)*R^(-1/2).
Since n<=a+1, the second term is O(exp(-9a/2)) for j<=n, while
eta^n*norm(p)<=exp(-7a/2). Hence
 norm(H^n p)=O(exp(-7a/2)), sum_{j<n}norm(H^j p)<=C''*exp(a/2).
This closes the gap in the earlier insufficient second-moment argument:
the number of moments grows with aperture, while the explicit atom budget
controls every newly created prime jump.

### 5. The actual source energy

Set u=(1/c)*sum_{j<n}(-H)^j p and r=p-Au=(-H)^n p.
Then norm(u)<=C''*exp(a/2)/c and norm(r)->0. Let v be the actual form
Riesz response, E=q(v)=Re<p,Jv>. Positivity of A gives

 2*Re<Au,Jv><=Re<A Jv,Jv>+Re<Au,u><=E+Re<Au,u>.

Using the exact source equation and physical coercivity therefore yields
 E<=Re<Au,u>+2*norm(r)*sqrt(E)
   <=2*c*norm(u)^2+2*norm(r)*sqrt(E).
The first term is bounded because exp(a)/c<=2. Young's inequality absorbs
half of E from the second term. Thus E is eventually bounded by one fixed
constant. On the remaining compact aperture interval, ordinary source
Cauchy--Schwarz and q>=physical mass give E<=norm(p)^2, also bounded.

## Formalization obligations

- [x] Exact prescribed shift lower bound; leaf audit passed.
- [x] Complete Mangoldt prefix estimate on the growing uniform window; direct leaf audit passed and umbrella import added.
- [x] All-polynomial completed-error and absolute-primitive cancellation; literal polynomial-frequency prime-polar symbol bound, direct leaf audits passed.
- [x] High-frequency cutoff specialization, continuous polar main term, and union of both frequency regions: CCMPolarPrimeExponentialFrequencyCancellation, direct leaf and five axiom audits passed.
- [x] Finite truncated-exponential representation and pointwise Fourier bound for every actual odd-source iterate: CCMFiniteExponentialRemainderOrbit, direct leaf audit35153 passed.
- [x] Integrated L2 Fourier tail bound for every actual odd-source iterate: CCMFiniteExponentialRemainderTail, direct leaf audit13836 passed.
- [x] Actual B closure with a fixed normalized budget factor, using the prescribed interval shift; same audited leaf.
- [x] Literal full-line multiplier/compression identity and one-step actual odd-orbit norm estimate: CCMRestrictedWeilPolarConvolution, CCMRestrictedWeilRemainderMultiplier and CCMRestrictedWeilSourceContraction; final leaf audits71723,23929,94938 passed.
- [x] Finite recurrence, exact Neumann residual, and actual odd-source energy weld: CCMRestrictedWeilFiniteNeumannSource and SuzukiMatchedOddSourceBound, final audits34076 and87048 passed.
- [x] Both new leaves wired; final leaf audits passed without warnings.
- [x] All five public axiom queries passed, standard Lean axioms only. Formal lint run: twelve unrelated unreachable modules, neither new leaf flagged; global lint remains non-green. Details in P3:sz-matched-odd-source-bound.
- [x] Literal finite-Neumann Gamma admission and actual matched physical-response decay: final leaves4687,84631,56559,13151,54388 passed; see P3:sz-matched-odd-physical-decay.
- [ ] Next hard target: growing physical coercivity and rescaled response-minus-Neumann error; see P1:sz-growing-physical-coercivity. Complete signed Wronskian remains open.

### Concrete low-frequency implementation

The existing Stieltjes integration-by-parts theorem requires zero terminal
test value. Apply it to exp(i*xi*h)-exp(i*xi*2a), then restore the constant
test through `criticalMellinStieltjesPairing_one`. This gives exactly
  pairing = exp(i*xi*2a)*D(2a)-integral_0^(2a) D(h)*i*xi*exp(i*xi*h) dh,
with D the literal completed critical-Mellin error. Hence its norm is at
most |D(2a)|+|xi|*integral_0^(2a)|D(h)| dh. Do not discard the endpoint.

For a direct rate transfer, use
`CCMActualHeadMatchedQuantilePolarDLVPRate.exists_abs_criticalMellinNormalizedChebyshevError_le_exp_half_sub_sqrt`
and `criticalMellinCompletedError_eq_volterraPotential`. If the driver
E(t) is eventually bounded by B*exp(t/2-c*sqrt(t)), split its primitive at
h/2. The compact head and the first half are O(1+exp(h/4)); the second
half is at most 2B*exp(h/2-c*sqrt(h/2)). Absorb the first half into that
envelope eventually. Thus D itself, and then its absolute primitive,
have bounds C*exp(h/2-c'*sqrt(h)), with c'>0. Multiplication by any fixed
power of h remains negligible after exp(-h/2). This proves the low
frequency estimate on the corpus's polylogarithmic frequency floor.
The generic preservation lemma was not found by search1185175 (partial,
source-only, no ingredient set). The final implementation below instead
uses the absolute primitive and all-polynomial limits; it does not require
this intermediate pointwise rate theorem.

## Next hard test

After the selected source bound, test the *signed* joint aperture quantity
O_a*D_e-E_a*D_o-(c_b-c_a)*(O_a*N_e-E_a*N_o). Absolute bounds on its separate
terms do not supply its sign or the required cofinal leakage estimate.
The normalization/shift obstruction documented in the main working log
also remains: this paper argument does not identify a Xi limit.

## Log

- 2026-10-02 — extracted finite-atom many-moment mechanism; wrote full
  paper candidate and checked its error accumulation. Shift leaf audited;
  arithmetic leaf under audit. RH remains unresolved.

Discrete high-frequency transfer, 2026-10-02: write G(k+1)=sum_{j<=k}g(j)
and w(k)=1/sqrt(k). Suppose norm(G(k+1))<=epsilon*(k+1) for M<=k<=N.
The Ioc Abel identity bounds the weighted tail by epsilon times
  w(N)*(N+1)+w(M+1)*(M+1)
    +sum_{M<k<N}(w(k)-w(k+1))*(k+1).
Apply the same identity to the constant sequence 1. This expression is
exactly sum_{M<k<=N}w(k)+2*w(M+1)*(M+1), at most 4*sqrt(N+1).
Thus the actual uniform Mangoldt prefix theorem gives the uniform weighted
tail bound 4*epsilon*sqrt(N+1), retaining every prime power and both cutoff
endpoints. This avoids both a frequency derivative and an artificial
logarithmic loss. The actual tail and retained-head prefix statements are
now audited in Sieve/VonMangoldtTwistHalfDensityWindow, wired, and checked
for axioms; only standard Lean axioms occur.

A shorter low-frequency proof avoids transferring a pointwise square-root
exponential rate twice. Set E=criticalMellinNormalizedChebyshevError and
J(h)=integral_0^h |E(t)|dt. Splitting at h/2 gives, eventually,
  J(h) <= (h/2)*(h+1)*exp(h/4)
          +2*B*exp(h/2-c*sqrt(h/2)).
The first half uses the actual global bound |E(t)|<=(2t+1)*exp(t/2);
the second half uses the actual PNT rate and the exact exponential
primitive. Therefore h^m*exp(-h/2)*J(h)->0 for every natural m, as does
the corresponding expression with |E(h)|. The exact completed-error
Volterra identity gives, for h>=0,
  |D(h)| <= 3+|E(h)|+J(h)/2.
Integrating once more and using monotonicity of J gives directly
  integral_0^h |D(t)|dt <= 3h+(1+h/2)*J(h).
Thus both D and its absolute primitive have the required all-polynomial
weighted cancellation. Only the absolute E primitive needs the half-cut
argument; no second generic rate-preservation theorem is necessary.
The final Stieltjes endpoint identity yields uniform cancellation for
|xi|<=(2a)^m. These steps now pass direct leaf audits in
CCMCriticalMellinPolynomialCancellation and
CCMPolarPrimePolynomialFrequencyCancellation; both are wired.

Further source-specific consequence to test after the bounded-energy weld:
the finite Neumann vector u is a truncated-exponential sum. Its small L2
norm and explicit Fourier tail should also give Gamma form energy
O(a*exp(-a)), by splitting the logarithmic Gamma weight at exp(K*a).
If the corpus Gamma/form-domain equivalence admits u, the actual form
residual v-u is controlled by the tiny Neumann residual plus that Gamma
form norm. This would give physical mass norm(Jv)^2=O(a*exp(-a)), stronger
than uniform source energy and directly relevant to the shift term in the
signed aperture expression. This is a new paper candidate, not a proved
consequence: form-domain admission and the actual residual identity must
both be formalized. It still would not determine the signed Wronskian.

The full exponential-frequency symbol theorem now passes its final leaf
audit and all five public axiom queries (standard axioms only), in
CCMPolarPrimeExponentialFrequencyCancellation. The exact proof and audit
are recorded in P3:sz-prime-polar-exponential-frequency. This closes the
arithmetic input to the proposed growing-iterate argument.

For the next finite-atom construction, source inspection verifies that
the actual polar operator is the sum of the two crossed rank-one maps
with profiles exp(x/2), exp(-x/2). Its compressed kernel is 2*cosh((x-y)/2).
Use V(z,s,l,r)=norm(z)*exp(max(s*l,s*r)) for each literal atom
z*1_[l,r](x)*exp(s*x). Translation by h replaces endpoints by l+h,r+h
and coefficient by z*exp(-s*h), preserving V exactly. Intersecting the
interval with the aperture cannot increase V; an empty intersection
vanishes. The Fourier antiderivative with denominator s-2*pi*i*xi gives
norm(Fourier(atom)(xi))<=V/(pi*abs(xi)), uniformly in interval length.
Summing these inequalities controls the complete atom sum with no
additional count factor. The corpus's HTGeometry/ExponentialPieceFourierDecay
contains the corresponding integer-frequency/unit-interval argument;
the required real-frequency, arbitrary-interval version is under audit.

For any atom sum supported in [-a,a] with total budget V, its pointwise
norm is <=V. Each of the two polar coefficients is bounded by
2*exp(a/2)*V, so the output polar budget is <=4*exp(a)*V. The symmetric
finite-prime terms cost <=42*exp(a)*V, and the scalar costs
abs(kappa)*exp(a)*V for a>=0. The audited shift lower bound therefore
normalizes the complete budget growth by a fixed aperture-independent
factor C0=2*(abs(kappa)+46). This must be welded to the actual Hilbert
operator, not assumed for an abstract replacement. Classical Fourier
uses angular frequency 2*pi*xi; absorb that fixed scale with an extra
unit in the exponential-window exponent when applying the symbol theorem.

The atom source estimates now pass final leaf audit4101 in
CCMTruncatedExponentialFourierBudget: pointwise bound, integrability,
exact real-frequency integral, inverse-frequency tail, exact translation,
translation-invariant budget, monotone restriction budget, finite-sum
Fourier decay, and literal aperture-intersection identity. Root umbrella
is wired; all nine axiom queries passed with standard axioms only. The finite-representation and
L2-tail checkbox remains open: these lemmas must still be assembled into
the actual remainder orbit and a quantitative L2 tail.

Next exact source conjecture: for every eta>0 and fixed K>0, eventually
in aperture a, each finite atom representation f supported in [-a,a]
with total endpoint budget V satisfies
  norm((B_a/c_a)f)<=eta*norm(f)+D*exp(-K*a/2)*V,
and the actual output admits a finite representation of budget <=C0*V,
with D,C0 independent of aperture and representation length. Prove the
first from the literal full-line multiplier, aperture compression, the
certified exponential-band cancellation, and the inverse-frequency tail.
Prove the second from the literal scalar, crossed polar maps, and prime
translations. Then run the stated growing-number-of-iterates argument.
The source condition is an explicit representation of the actual input,
not an assumed regularity or cancellation premise for the response.

Next physical-response paper test, 2026-10-02: source inspection verifies
the global exact-Gamma/log-weight comparison and the exact form-domain
transport. After admitting the finite Neumann vector u as a form vector g,
let z=w-g, where w is the actual odd Riesz response. The full form equation
gives q(z)=Re<r,Jz>-Re<g,z>_Gamma. Since q(z) pays both Gamma norm and
physical mass, Cauchy--Schwarz gives q(z)<=2*(norm(r)^2+norm(g)_Gamma^2).
The low/high Fourier split should give norm(g)_Gamma^2=O(a*exp(-a));
the previously retained exponential residual is smaller. Hence
norm(Jw)^2=O(a*exp(-a)). The literal form-domain admission and this actual
residual identity remain to be proved in Lean. Even that result alone
does not settle the signed combination of even/odd masses with the
growing shift, nor the canonical normalization or Xi identification.

Concrete logarithmic estimate for that next test: if f has certified
finite-exponential budget V and R>=1, its literal Fourier representative
g satisfies
  integral (1+max(log|xi|,0))*|g(xi)|^2
    <= (1+log R)*norm(f)^2 + (2V^2/pi^2)*(log R+2)/R.
The low band uses Plancherel; each tail uses the certified inverse-frequency
envelope and the exact integral of (1+log x)/x^2 on (R,infinity).
This also proves weighted-L2 admission, not just a bound on an assumed
form-domain vector. The exact Gamma/log-weight comparison transfers it
to the actual form domain while preserving aperture support.
For the literal Neumann vector, V_u<=exp(a/2)*C0^ceil(a)/c_a,
norm(u)<=M*exp(a/2)/c_a, and R=exp((2log C0+10)*a).
Thus the weighted tail is O(a*exp(-11a)) and the low band O(a*exp(-a)).
The quantitative residual O(exp(-7a/2)) from the finite recurrence must
be exported explicitly; the currently formalized uniform residual bound
alone is insufficient for this stronger physical-mass conclusion.
