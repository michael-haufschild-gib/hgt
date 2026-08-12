# Marked Mellin normalization, exchange, and phase-response law

- **ID:** `cmr-marked-mellin-normalization-exchange-response`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / LOCAL NORMALIZATION-RESPONSE LAW
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [HOSTILE-ACCEPTED]`
  `[THREE-REPORTER COMPATIBILITY] [ANALYTIC EXCHANGE SEED]`
  `[DENSE ATOMIC SOURCE NERVE] [NOT RH] [LEAN-FORMALIZED UNCONDITIONALLY]`
- **Formalized companion:** `marked-mellin-normalization-exchange-response-law-formalized.md`
  (same directory).
- **Parent chart:** `marked-euler-shell-mellin-gns-ht-recurrence-normalization-wall-law.md`.
- **Statement:** Positive coefficient streams have a countable, fully faithful atomic source nerve.
  Marked Mellin normalization has one-dimensional radial kernel. Its differential is a centered
  signed-measure exchange tangent, and evaluation on the phase character gives an exact covariance
  response law. Forgetting total mass preserves normalized states and phase history but destroys
  absolute source-response identifiability.

## 1. Smooth coefficient source and atomic probes

Fix `sigma>1`. Let `C_sigma^infinity` be the poset, under coordinatewise order, of nonzero streams

\[
 c=(c_n)_{n\ge2},\qquad c_n\ge0,
\tag{MER.1}
\]

such that, for every integer `k>=0`,

\[
 M_k(c)=\sum_{n\ge2}c_n n^{-\sigma}(\log n)^k<\infty.
\tag{MER.2}
\]

The ambient real Fréchet space is

\[
 X_\sigma=\left\{h:
 p_k(h)=\sum_{n\ge2}|h_n|n^{-\sigma}(1+\log n)^k<\infty
 \text{ for every }k\right\},
\tag{MER.2a}
\]

with its projective-limit topology. It is complete as the projective limit/intersection of the
weighted `ell^1` spaces. The source poset is the nonzero positive cone
`C_sigma^infinity=X_(sigma,+)\setminus{0}`. It is closed under finite sums, positive scaling, and
finite coordinatewise suprema. No arbitrary-join claim is made.

For `q in Q_(>0)` and `n>=2`, let `p_(n,q)=q e_n`. These probes belong to
`C_sigma^infinity`. Let `P_at` be their full subposet and `J:P_at->C_sigma^infinity` the inclusion.
Define the restricted source nerve, with structure maps given by precomposition,

\[
 N_J:C_\sigma^\infty\longrightarrow
 \operatorname{Set}^{P_{\rm at}^{\rm op}},
 \qquad N_J(c)(p)=\operatorname{Hom}(Jp,c).
\tag{MER.3}
\]

### Theorem 1.1 — atomic source density

`N_J` is fully faithful. Equivalently, for `c,d in C_sigma^infinity`, a natural transformation
`N_J(c)->N_J(d)` exists exactly when `c<=d`, and it is then unique. Moreover `c` is the supremum,
inside `C_sigma^infinity`, of the category-of-elements diagram of all rational atomic probes below
it.

### Proof

Every hom-set in a poset is empty or a singleton. The support of `N_J(c)` is

\[
 \{(n,q):q\le c_n\}.
\]

A natural transformation between two such subterminal presheaves exists exactly when the first
support is contained in the second. By density of positive rationals, this says
`c_n<=d_n` for every `n`, hence `c<=d`. Uniqueness is automatic. For fixed `c`, coordinatewise the
supremum of all `q e_n<=c` has `n`-th coordinate
`sup({0} union {q in Q_(>0):q<=c_n})=c_n`; it is `c`, which already lies in the declared source
poset. The added `0` covers zero coordinates; the probe diagram is nonempty because `c!=0`. QED.

This is a literal countable probe family, not the tautological choice of every source object.

## 2. Three source reporters

For `c in C_sigma^infinity`, define

\[
 S_c(s)=\sum_{n\ge2}c_n n^{-s},\qquad \Re s\ge\sigma,
\tag{MER.4}
\]

The derivative series converge absolutely and uniformly on `Re s>=sigma`. Hence `S_c` is
holomorphic on `Re s>sigma`, every holomorphic derivative has a continuous boundary value, and
the vertical boundary path `t->S_c(sigma+it)` is smooth. Define the unnormalized positive measure

\[
 \mu_c=\sum_{n\ge2}c_n n^{-\sigma}\delta_{\log n},
 \qquad Z_c=\mu_c(\mathbb R)=S_c(\sigma)>0.
\tag{MER.5}
\]

Its normalization and phase correlation are

\[
 P_c=Z_c^{-1}\mu_c,
 \qquad
 C_c(t)=\int e^{-itx}\,dP_c(x)
       =\frac{S_c(\sigma+it)}{S_c(\sigma)}.
\tag{MER.6}
\]

Thus the same source has:

1. a differential/Mellin reporter `S_c`;
2. a marked positive reporter `(Z_c,P_c)`;
3. a history/phase reporter `C_c`.

The unnormalized measure, and equivalently the marked pair `(Z_c,P_c)`, is coefficient-faithful:

\[
 c_n=n^\sigma\mu_c(\{\log n\})
    =Z_c n^\sigma P_c(\{\log n\}).
\tag{MER.7}
\]

The unmarked probability `P_c` is invariant under every positive radial rescaling `c->lambda c`.

## 3. Normalization exchange seed

Let `M_sigma^infinity` be the Fréchet space of atomic signed measures with seminorms
`q_k(nu)=int(1+|x|)^k d|nu|(x)`. The maps `h->mu_h` and `H_0` are continuous linear maps from
`X_sigma` to `M_sigma^infinity` and `R`. On the open signed halfspace

\[
 U_\sigma=\{x\in X_\sigma:H_0(x)>0\},
\]

the normalization map `P(x)=mu_x/H_0(x)` is smooth as a composition of continuous linear maps,
scalar inversion, and multiplication. The positive source cone lies in `U_sigma`. Let
`h=(h_n) in X_sigma`, equivalently

\[
 \sum_n |h_n|n^{-\sigma}(1+\log n)^k<\infty
\tag{MER.8}
\]

for every `k`. If a source path is required, additionally suppose `c+epsilon h` is nonnegative in
the appropriate one-sided or two-sided neighbourhood of `0`. The derivative below is the ambient
Fréchet derivative on `U_sigma`, restricted to such paths. Put

\[
 \mu_h=\sum_n h_n n^{-\sigma}\delta_{\log n},
 \qquad H_0(h)=\mu_h(\mathbb R).
\tag{MER.9}
\]

### Theorem 3.1 — exact normalization exchange

The directional derivative of normalization is

\[
 D P_c[h]
 =\frac1{Z_c}\left(\mu_h-H_0(h)P_c\right).
\tag{MER.10}
\]

It has total mass zero. Its kernel is precisely the radial line:

\[
 D P_c[h]=0
 \quad\Longleftrightarrow\quad
 h=\alpha c
\tag{MER.11}
\]

on all coordinates. For a one-sided positive tangent cone, its zero-response set is the
intersection of this radial kernel with that cone. Consequently normalization is locally the
quotient by positive source scale, not a quotient by phase.

### Proof

Differentiate

\[
 P_{c+\epsilon h}
 =\frac{\mu_c+\epsilon\mu_h}{Z_c+\epsilon H_0(h)}
\]

at `epsilon=0`, giving `(MER.10)`. Its mass is
`Z_c^(-1)(H_0(h)-H_0(h))=0`. At every atom,

\[
 DP_c[h](\{\log n\})
 =\frac{n^{-\sigma}}{Z_c}
  \left(h_n-\frac{H_0(h)}{Z_c}c_n\right).
\]

Thus vanishing forces `h_n=(H_0(h)/Z_c)c_n` for every `n`, including coordinates where `c_n=0`.
Hence `h=alpha c` globally. The converse is immediate. QED.

The centered signed measure

\[
 \mathcal E_c(h)=\mu_h-H_0(h)P_c
\tag{MER.12}
\]

is the nonidentity analytic exchange seed. It is defined before selecting any Xi zero. No indexed
PCDG multicell has yet been constructed from it.

## 4. Constitutive phase-response equation

### Theorem 4.1 — source intervention equals centered phase response

For every admitted `h`,

\[
 D C_c[h](t)
 =\frac1{Z_c}\sum_{n\ge2}h_n n^{-\sigma}
       \left(n^{-it}-C_c(t)\right)
 =\int e^{-itx}\,d(DP_c[h])(x).
\tag{MER.13}
\]

If `h_n=c_n r_n` for a bounded real score `r`, then

\[
 D C_c[h](t)
 =\operatorname{Cov}^{\rm bil}_{P_c}\!\left(r,e^{-itx}\right),
\tag{MER.14}
\]

where `Cov_bil(f,g)=E(fg)-E(f)E(g)` is the bilinear covariance used for the complex phase
character. Values of `r` off the active support are irrelevant. For the multiplicative atom intervention
`h=c_Ne_N`,

\[
 D C_c[c_Ne_N](t)
 =P_c(\{\log N\})\left(N^{-it}-C_c(t)\right).
\tag{MER.15}
\]

The phase response is therefore predicted by the marked positive reporter and the current phase
correlation; it is not separately fitted.

### Proof

Differentiate the quotient in `(MER.6)`:

\[
 D C_c[h](t)
 =\frac{\left(\sum h_nn^{-\sigma-it}\right)Z_c
       -S_c(\sigma+it)H_0(h)}{Z_c^2},
\]

which is `(MER.13)`. Substitution `h=cr` gives `(MER.14)`, and the one-atom case gives
`(MER.15)`. Absolute convergence follows from `(MER.8)`. QED.

## 5. Fisher-cost bound and time jets

For a bounded real score `r`, put

\[
 g_c(r,r)=\operatorname{Var}_{P_c}(r).
\tag{MER.16}
\]

For complex `g`, define the Hermitian variance

\[
 \operatorname{Var}_{P_c}^{H}(g)
 =\mathbb E_{P_c}|g-\mathbb E_{P_c}g|^2.
\]

Then Cauchy--Schwarz gives

\[
 |D C_c[cr](t)|^2
 \le g_c(r,r)\operatorname{Var}_{P_c}^{H}(e^{-itx})
 =g_c(r,r)(1-|C_c(t)|^2)
 \le g_c(r,r).
\tag{MER.17}
\]

Thus the quotient Fisher seminorm bounds every phase-character response, and its kernel consists
of scores constant `P_c`-almost surely. Under `h=cr`, this is exactly the radial source direction
on the active support.

All time jets are admitted by `(MER.2)` and satisfy

\[
 \partial_t^k C_c(t)
 =(-i)^k\int x^k e^{-itx}\,dP_c(x).
\tag{MER.18}
\]

More exactly,

\[
 \partial_t^k D C_c[h](t)
 =\frac{(-i)^k}{Z_c}\left(
   \int x^k e^{-itx}\,d\mu_h
   -H_0(h)\int x^k e^{-itx}\,dP_c\right)
 =D\!\left(\partial_t^k C_{\bullet}(t)\right)_c[h].
\tag{MER.18a}
\]

Dominated convergence uses the available absolute log moments. This is an analytic
three-reporter compatibility prototype; no indexed PCDG multicell is constructed.

## 6. Exact non-identifiability after unmarked normalization

### Countertheorem 6.1 — normalized state cannot predict absolute intervention response

Fix `lambda>0` with `lambda!=1`. The sources `c` and `lambda c` have identical unmarked positive
reporter and phase history:

\[
 P_{\lambda c}=P_c,
 \qquad C_{\lambda c}=C_c.
\tag{MER.19}
\]

For the same absolute additive intervention `h`, however,

\[
 D C_{\lambda c}[h](t)=\lambda^{-1}D C_c[h](t).
\tag{MER.20}
\]

Such a nonzero admitted response always exists. If `P_c` is not Dirac, choose an active `N` with
`log N!=E_(P_c)x` and put `h=c_Ne_N`, a two-sided admitted intervention. Differentiating
`(MER.15)` at `t=0` gives

\[
 \left.\partial_tD C_c[c_Ne_N](t)\right|_{t=0}
 =-iP_c(\{\log N\})(\log N-E_{P_c}x)\ne0.
\]

If `P_c=delta_(log N)`, choose `M!=N` and the one-sided admitted intervention `h=e_M`. Then

\[
 D C_c[e_M](t)
 =\frac{M^{-\sigma}}{Z_c}(M^{-it}-N^{-it}),
\]

which is nonzero whenever `t(log M-log N)` is not in `2pi Z`. Hence for every source and every
`lambda!=1`, some absolute intervention distinguishes the responses. No rule factoring only
through `(P_c,C_c)` can
recover absolute source response. Marking `Z_c`, or equivalently the unnormalized measure, repairs
the loss.

### Proof

Equation `(MER.19)` is radial invariance. Substitute `Z_(lambda c)=lambda Z_c` and
`C_(lambda c)=C_c` into `(MER.13)` to obtain `(MER.20)`. QED.

For `lambda!=1`, `c` and `lambda c` are nonisomorphic in the source poset, so full faithfulness
gives `N_J(c) not~=N_J(lambda c)`, whereas their unmarked probability objects agree. More
generally, for any functor `Q:C_sigma^infinity->A` satisfying
`Q(c)~=Q(lambda c)`, there cannot exist `B:A->Set^(P_at^op)` and a natural isomorphism
`N_J~=B Q`. This is the exact object-reflection consequence of dense-source non-descent.
The current assignment `c->P_c` has not itself been typed as a functor on coordinatewise source
arrows, so its equality is an object-level obstruction consistent with that theorem, not yet a
constructed doctrine exit.

## 7. Euler-shell specialization

For `c=a_m`, `m>=12`, the parent theorem supplies genuine analytic HT of the corresponding
`H_m`, compact-resolvent recurrent GNS dynamics, divergent unwrapped history, and Mass/Weil/phase
prime shadows. The present theorem adds source interventions and a nonidentity constitutive
response equation on its positive fibres `sigma>1`.

It does not cross the parent normalization wall to physical half-density. It does not realize
Route E, G, L, O, R, Mass affine successor, or Stokes source dagger. No RH selector or
null-homology is claimed.

## 8. Conjecture/proof/failure loops

### Loop A — normalized probability is the complete positive source geometry

**Failed by Countertheorem 6.1.** It loses source scale and absolute intervention response.

**Survivor.** Retain `(Z,P)`, not `P` alone, whenever source interventions are absolute.

### Loop B — positivity erases phase

**Failed in this chart.** The positive measure determines every phase correlation by Fourier
evaluation. The information loss here is radial normalization, not phase.

**Survivor.** Compute the fibre of each named positive reduction; do not infer it from positivity.

### Loop C — HT causes noncompact observed dynamics

**Failed by the Euler-shell parent.** Genuine HT coexists with compact-resolvent, norm-precompact
recurrent observation.

**Survivor.** Differential jet growth, phase history, and normalization singularity are linked
only by explicit comparison equations such as `(MER.13)` and `(MER.18)`.

### Loop D — a category alone supplies dynamics

**Failed.** Atomic density reconstructs sources but does not determine normalization or response.

**Survivor.** The field needs both the dense source nerve and constitutive exchange cell
`(MER.10)`.

## 9. Scope and hostile gate

This theorem closes a small but real part of the proposed three-doctrine gate:

1. a non-singleton source category and countable fully faithful source nerve are explicit;
2. differential/Mellin, marked positive, and phase/history reporters are explicit;
3. normalization exchange and phase response are explicit and nonidentity analytic seeds;
4. an unmarked exit has an exact identifiability countermodel.

It does **not** construct differential/HT, positive, and history as indexed PCDG fibres; type source
interventions as categorical arrows; construct a represented multicell; prove constitutive Morita
invariance; or predict a response in an independent fourth corpus organ. Those remain the next
field-level test.

## 10. Literature boundary

Normalization, score covariance, Fisher seminorms, and response inequalities are classical
probability/information geometry. Categorical normalization and observation are also developed in
partial Markov categories (Di Lavore--Roman--Sobocinski, arXiv:2502.03477). The theorem does not
claim those ingredients as new. Its role is to compute their exact coupling on the marked HGT
coefficient/Mellin source and to expose the radial identifiability obstruction before any Xi
specialization. It remains a local calibration until a heterogeneous source-natural multicell and
independent fourth-organ prediction are constructed.

## Lean-return note

No Lean code was written or built. Later formalization can use finite-support coefficient streams,
finite atomic probability measures, quotient differentiation, and Cauchy--Schwarz before any
infinite-series layer.
