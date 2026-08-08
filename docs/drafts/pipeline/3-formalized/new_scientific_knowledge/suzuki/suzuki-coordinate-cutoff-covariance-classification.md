# Coordinatewise terminal cutoffs cannot commute with Suzuki's valuation transport

- **ID:** `suzuki-coordinate-cutoff-covariance-classification`
- **Stage:** 3-formalized
- **Type:** EXACT CUTOFF/TRANSPORT CLASSIFICATION AND PROOF-ARCHITECTURE NO-GO
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Lean:** `GaloisForLFunctions.RHTower.SuzukiCoordinateCutoffCovariance`
- **Killed claim:** the “harmless coordinatewise initial cutoff” in
  `suzuki-finite-recurrence-trace-zero-h1-conjecture.md`
- **Primary-source boundary:** Suzuki 2026 constructs the fixed-aperture closed form and explicitly
  warns that pointwise values need not exist on the operator domain; Chen--Weth and
  Hernández-Santamaría--López Ríos--Saldaña give logarithmic-Laplacian form and optimal boundary
  regularity, but no translated valuation-orbit cutoff theorem.

## 1. Classification theorem

Let \(G=\mathbb Z^d\), let \(\Sigma\subset G\) generate \(G\), and let

```text
(S_s Z)_nu = alpha_(s,nu) Z_(nu+s),       alpha_(s,nu) != 0              (1)
```

be any family of weighted valuation shifts.  Let
\(\chi_\nu:\mathbb R\to\mathbb C\) be locally Lipschitz and let

```text
(M_chi Z)_nu(L)=chi_nu(L)Z_nu(L).                               (2)
```

For every smooth finitely supported orbit profile \(F\),

```text
([M_chi,S_s] partial_L F)_nu
 =alpha_(s,nu)[chi_nu-chi_(nu+s)] partial_L F_(nu+s).            (3)
```

Consequently the following are equivalent:

```text
[M_chi,S_s] partial_L F=0
for every smooth finitely supported F and every s in Sigma;

chi_nu=chi_(nu+s) a.e.
for every nu and s in Sigma;

there is one scalar cutoff chi with chi_nu=chi for every nu.     (4)
```

Now prescribe terminal validity times \(\tau_\nu\) and require an adapted cutoff:

```text
chi_nu(L)=0,  L<=tau_nu;
chi_nu(L)=1,  L>=tau_nu+1.                                      (5)
```

If the family \(\{\tau_\nu\}\) is unbounded above, no family satisfying `(5)` can satisfy
the equivalent covariance conditions `(4)`.

Finally, if `(4)` fails on one active edge, the derivative commutator in `(3)` has no
zero-order \(L^2\) estimate: there is no constant \(C\) such that

```text
||[M_chi,S_s] partial_L F||_(L2_L ell2_G)
 <=C ||F||_(L2_L ell2_G)                                       (6)
```

for every smooth compactly supported \(F\).

Thus a coordinatewise terminal cutoff can be adapted to unbounded orbit event times or commute
with prime transport, but not both.  If it is adapted, treating its differentiated prime
commutator as an \(L^2\) source already assumes the derivative regularity that the argument is
supposed to prove.

The conclusion is unchanged by:

- exponential valuation weights;
- finite recurrence type \(\tau_\nu=O(|\nu|_1)\);
- nonnormal rather than self-adjoint weighted adjacency;
- arbitrarily large terminal multiplication \(2L\).

Those features change sizes, not the derivative order in `(3)`.

## 2. Proof of the commutator identity

At coordinate \(\nu\),

```text
(M_chi S_s partial_L F)_nu
 =chi_nu alpha_(s,nu) partial_L F_(nu+s),

(S_s M_chi partial_L F)_nu
 =alpha_(s,nu) chi_(nu+s) partial_L F_(nu+s).            (7)
```

Subtracting gives `(3)`.

Suppose the first line of `(4)` holds.  Fix an edge \((\nu,\nu+s)\), choose a scalar smooth
function \(f\) with \(f'\) nonzero on any prescribed compact subinterval, and take \(F\) supported
only at \(\nu+s\) with that coordinate equal to \(f\).  Since
\(\alpha_{s,\nu}\ne0\), `(3)` forces

```text
chi_nu=chi_(nu+s) a.e.                                  (8)
```

Local Lipschitz regularity upgrades the equality to equality of the continuous representatives.
Conversely `(8)` makes `(3)` zero.  Since \(\Sigma\) generates \(G\), concatenate generator
edges from \(0\) to any \(\nu\); `(8)` then gives
\(\chi_\nu=\chi_0\).  This proves `(4)`. `QED`

## 3. Unbounded event times exclude one common adapted cutoff

Assume `(4)` and write the common cutoff as \(\chi\).  Choose any root label \(\nu_0\).  Condition
`(5)` gives

```text
chi(L)=1,  L>=tau_(nu_0)+1.                              (9)
```

Because the validity times are unbounded, choose \(\nu_1\) with

```text
tau_(nu_1)>tau_(nu_0)+1.                                 (10)
```

At \(L=\tau_{\nu_0}+1\), `(5)` for \(\nu_1\) gives \(\chi(L)=0\), contradicting `(9)`.
Thus no common adapted cutoff exists. `QED`

For Suzuki's two-ended valuation orbit the relevant event times include

```text
tau_nu=[-log|ell(nu)|]_+
and
tau'_nu=[-log|2a-ell(nu)|]_+.                            (11)
```

Whenever either family is unbounded, the theorem applies.  Finite recurrence type only supplies
the upper bound

```text
tau_nu+tau'_nu=O(1+|nu|_1);                              (12)
```

it does not make the family bounded.

## 4. The derivative commutator is genuinely first order

Suppose \(\chi_\nu-\chi_{\nu+s}\) is not identically zero.  By continuity there are an interval
\(J\), a number \(\delta>0\), and a nonzero
\(\phi\in C_c^\infty(J)\) such that

```text
|alpha_(s,nu)[chi_nu(L)-chi_(nu+s)(L)]|>=delta
on supp(phi).                                           (13)
```

Put

```text
F^(N)_(nu+s)(L)=phi(L)exp(iNL),
F^(N)_mu=0 for mu!=nu+s.                                (14)
```

Then \(\|F^{(N)}\|_2=\|\phi\|_2\), while `(3)` and the reverse triangle inequality give

```text
||[M_chi,S_s]partial_L F^(N)||_2
 >=delta[N||phi||_2-||phi'||_2].                        (15)
```

The right side tends to infinity.  This disproves `(6)`. `QED`

This is not a pathology of oscillatory test profiles.  It says exactly that the proposed source
norm has lost one derivative across a cutoff that fails transport covariance.

## 5. Literal consequence for the finite-recurrence proof

The attempted paired-orbit proof takes one terminal cutoff for each valuation label because the
physical equation is available only after that label's last boundary event.  Its differentiated
prime block is

```text
B_(a,w) F'.                                              (16)
```

After cutoff, the exact equation contains

```text
[M_chi,B_(a,w)]F'.                                      (17)
```

Every active prime-power coefficient is nonzero.  Therefore `(3)`--`(4)` apply edge by edge.
For dense two-prime valuation orbits the event times are unbounded, so `(5)` rules out a commuting
cutoff.  Equation `(15)` rules out estimating `(17)` from the already known bounded or
\(L^2\) profile norm.

The statements

```text
R(a)<infinity,
sum_nu w(nu)^2 exp(2sigma tau_nu)<infinity               (18)
```

do control zero-order event sources such as \(\chi_\nu'F_\nu\).  They do not control `(17)`.
Hence `(18)` cannot prove the differentiated Gamma block source theorem without an independent
graph norm containing \(F'\).  Using that graph norm would be circular for the target
\(F'\in e^{-\sigma L}L^2\).

Therefore:

```text
finite recurrence
 -> zero-order event summability;                        [SURVIVES]

finite recurrence
 -> differentiated orbit source in weighted L2;         [NOT PROVED;
                                                          CUTOFF ARCHITECTURE BLOCKED]

finite recurrence + zero endpoint traces
 -> H1_0;                                                [OPEN]              (19)
```

The theorem statement in the killed card is not disproved; its proposed proof is.

## 6. Positive survivor and stronger conjecture

The obstruction says what a viable representation must retain: terminal validity cannot be
implemented by a diagonal cutoff after the prime coupling has been differentiated.

Three exact alternatives remain:

1. keep Suzuki's whole-line exterior residual in a closed graph/distribution source space and use
   one common physical cutoff before orbit localization;
2. assemble the **undifferentiated** paired equation, for which
   \([M_\chi,B]F\) is zero order, and derive the derivative only after a global flux identity;
3. construct a transport-covariant non-diagonal projection whose range already contains the
   boundary-event relation.

The first and third retain the exterior residual; the second retains the primitive seam response.
All remove the false source estimate exposed by `(17)`.

The strongest live replacement is:

```text
SUZUKI-PRIMITIVE-ORBIT-FLUX:

the exact undifferentiated weighted orbit equation admits a global
boundary-event flux law whose event terms are controlled by (18);
zero physical half-log traces and zero seam jump then force
the differentiated root profiles into one Gamma weight sigma>1/2.          (20)
```

`(20)` is stronger structurally than repairing `(17)` with an ad hoc norm: it predicts a conserved
primitive flux that explains why derivative loss cancels.  The commutator no-go does not apply
because no label-dependent cutoff is commuted across \(B\partial_L\).

`[OPEN CORE]` Construct that exact flux from Suzuki's supported whole-line equation, or prove that
every transport-covariant boundary-event relation necessarily contains an uncontrolled exterior
charge.

## 7. Hostile and novelty audit

1. **No false theorem verdict.**  The finite-recurrence \(H^1_0\) statement remains open; only its
   present proof is invalid.
2. **No recurrence confusion.**  Linear growth of event times is not boundedness of event times.
3. **No self-adjointness issue.**  The obstruction is algebraic and holds for weighted nonnormal
   shifts.
4. **No norm handwave.**  `(14)`--`(15)` explicitly disprove every zero-order \(L^2\) estimate.
5. **No patched survivor.**  `(20)` changes from differentiated diagonal localization to primitive
   global flux.
6. **Literature boundary.**  Commutator identities and unboundedness of differentiation on \(L^2\)
   are standard.  Searches of Suzuki's source paper and logarithmic-Laplacian boundary literature
   found no valuation-orbit/event-time classification `(3)`--`(19)`.  External priority for the
   source-specific conjunction is unverified.

Candidate-new content is the sharp trilemma

```text
transport covariance
+ event-adapted terminal localization
+ zero-order differentiated source control:
at most two can hold on an unbounded Suzuki valuation orbit.               (21)
```

## 8. Lean target

`SuzukiCoordinateCutoffCovariance.lean` formalizes exactly:

- weighted-shift/diagonal-multiplier commutator `(3)`;
- edgewise equality forced by vanishing commutator;
- propagation of equality along finite generator words;
- incompatibility of a common cutoff with two ordered validity thresholds.

The analytic high-oscillation corollary `(15)` requires Sobolev/Fourier infrastructure and must not
be replaced by a finite-dimensional wrapper.  Until that exact analytic corollary is formalized,
the card remains Stage 2.

## Gates

- [x] compute exact derivative commutator
- [x] classify all transport-covariant diagonal cutoffs
- [x] prove unbounded validity times exclude an adapted covariant cutoff
- [x] disprove every zero-order \(L^2\) commutator estimate
- [x] identify finite recurrence as zero-order, not first-order, control
- [x] retract the invalid finite-type proof architecture
- [x] extract primitive global-flux survivor
- [ ] construct or refute `SUZUKI-PRIMITIVE-ORBIT-FLUX`
- [x] formalize covariance/event-order core unconditionally in Lean
- [ ] formalize high-oscillation \(L^2\) corollary
- [ ] prove trace-zero supported-nullspace theorem
- [ ] prove RH or a genuine whole-Connes no-go
