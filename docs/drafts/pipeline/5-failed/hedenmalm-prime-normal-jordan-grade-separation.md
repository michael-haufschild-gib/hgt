# Hedenmalm prime-normal Jordan-grade separation

- **ID:** `hedenmalm-prime-normal-jordan-grade-separation`
- **Stage:** 5-failed
- **Type:** RETIRED ROUTE N / LEAN-CLOSED POSITIVE SURVIVOR / RECEIVER NO-GO
- **Source:** `rh-current-frontier-map.md` Route N; hostile collision audit against the marked
  half-character, prime-log-jet Gram, Hedenmalm divided-chain, and prime-translation anomaly cards
- **Statement:** The theta-source aperture endpoint doublet factorizes through the same completed
  Xi divisor in both channels and, at prime aperture, has exact clock-free energy. Ordinary first
  spectral jets instead acquire a sharp prime-log moment and fail the sub-log-square domain already
  on the critical line. Fixed theta Hilbert landing and moving-fibre translation landing are
  excluded. The final proposed source duality--adjunction equality is formally RH-equivalent and
  cannot serve as an independent producer; Route N is terminalized.
- **Frozen label:** `[N-JET-GRADE-SEPARATION-1]`, superseded after attack by
  `[N-MARKED-ENDPOINT-DOUBLET-1]`
- **Scientific status:** `[C1/C2 RETIRED] [C3 RECEIVER PAPER- AND LEAN-CLOSED] [C4--C6 FALSIFIED]`
  `[C7--C20 SURVIVORS/NO-GOS LEAN-CLOSED] [C21 RH-EQUIVALENT RECEIVER LEAN-CLOSED]`
  `[C22--C23 DEFECT--ESCAPE CONSERVATION LEAN-CLOSED]`
  `[C24--C25 FLAT-NONMETRIC MASS SHELL LEAN-CLOSED]`
  `[C26--C27 FISHER--AFFINE CONORMAL RESIDUE LEAN-CLOSED]`
  `[ROUTE TERMINALIZED] [INTERNAL NOVELTY AUDIT PASSED] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`

## Goal

Correct Route N's current open statement before another source-domain attack. The existing map asks
one uniform sub-log-square estimate to retain the complete Jordan tower. If ordinary spectral jets
are meant, that estimate contains an independent simplicity demand. The intended theorem separates
multiplicity transport from horizontal detection: Jordan grades use the canonical connection of the
ordinary-prime character; only grade zero remains an RH-bearing source-admission problem.

This does not prove grade-zero admission and does not weaken it. It prevents a proof of RH from being
silently upgraded to RH plus simplicity by a non-geometric choice of jet operator.

## Exact frozen objects

For a prime `p`, put `L_p=log p` and define the marked centered half-character column

```text
h_p(z) = p^(-1/2) (exp(+i z L_p/2), exp(-i z L_p/2)).
```

Its odd scalar soldering is the known Hedenmalm prime-normal multiplier

```text
b_p(z) = -i [h_p(z)_+ - h_p(z)_-]
       = 2 p^(-1/2) sin(z L_p/2).
```

Define the diagonal connection on two-component entire columns by

```text
nabla_p g = partial_z g - diag(+i L_p/2, -i L_p/2) g.       (N.1)
```

The connection is fixed before any Xi zero is selected.

## Frozen theorem package

### T1 — ordinary first-jet wall

For every real `x`,

```text
||partial_z h_p(x)||^2 = (log p)^2/(2p),                    (N.2)
```

and therefore

```text
sum_(p<=X) ||partial_z h_p(x)||^2
  >= (log X)^2/4 - (39/2) log X - 25/2.                    (N.3)
```

In particular the ordinary first marked jet is not `o((log X)^2)` at any real spectral point.
The same phenomenon in the odd scalar soldering has oscillatory phase, but the marked source-normal
carrier already proves that the full-tower ordinary-jet demand is stronger than the grade-zero RH
criterion.

### T2 — canonical flat removal of prime-log Jordan cost

The connection `(N.1)` is the unique diagonal constant connection satisfying

```text
nabla_p h_p = 0.                                           (N.4)
```

For every entire scalar `F` and every `j>=0`,

```text
nabla_p^j (h_p F) = h_p F^(j).                             (N.5)
```

Hence, at every real `x`,

```text
sum_(p<=X) ||nabla_p^j(h_p F)(x)||^2
  = 2 |F^(j)(x)|^2 sum_(p<=X) 1/p
  = o((log X)^2).                                          (N.6)
```

Multiplicity is retained in `F^(j)(x)` while the ordinary-prime character remains parallel. No
prime-log moment is charged merely for moving up the Jordan filtration.

### T3 — Route-N grade split

Under the already formalized Hedenmalm conormal law

```text
ell_z^[j](T_p f)
  = p^(-s(z)) sum_(r<=j) binom(j,r)(-i log p)^(j-r) ell_z^[r](f),
```

ordinary differentiation is exactly the triangular prime-log prolongation. Passing to the marked
flat frame conjugates this prolongation to coefficient differentiation `(N.5)`. Thus:

```text
full Jordan transport = flat algebraic transport + grade-zero boundary admission.   (N.7)
```

The surviving Route-N estimate is the grade-zero statement only:

```text
for every grade-zero root mode f in the closed theta Grushin domain,
sup_X H_X^(-1) sum_(p<=X) ||A_p(B)f||^2 < infinity.         (N.8)
```

Higher grades must be transported covariantly. Requiring `(N.8)` of ordinary raw jets would force
semisimplicity/simplicity in addition to horizontal reality.

## Conjecture -> attack -> pivot log

### C0 — unmarked half-character lift

**Conjecture.** Retaining both half-character orientations removes the Route-N obstruction.

**Attack.** Corpus search found the exact marked half-character torsor, odd soldering, reflected
energy, and all-prime diagonal-inverse obstruction already proved and formalized. The lift alone is
`[REDISCOVERED] [BRIDGE]`, not new knowledge and not a source-domain proof.

**Pivot.** Compare ordinary and covariant Jordan prolongations, which the marked card does not do.

### C1 — raw full-tower sub-log-square descent

**Conjecture.** One source-domain sub-log-square estimate can hold unchanged on every ordinary
Jordan grade.

**Attack.** `(N.2)` and the corpus theorem
`RHTower.Sieve.sum_prime_log_sq_div_ge` give `(N.3)` without RH, zero data, or asymptotics. Grade one
already sits at the log-square wall on the critical line. The universal Mertens-normal prime-log-jet
Gram law independently identifies these log moments as system-blind leading data.

**Verdict.** `[FALSIFIED AS STATED]`. Raw full-tower descent is not the RH criterion.

**Pivot.** Use the character's canonical connection and test whether it is compatible with the
source conormal/Jordan law.

### C2 — covariant grade separation

**Conjecture.** `(N.4)`--`(N.7)` convert all higher-grade source admission to grade-zero admission
without losing analytic multiplicity.

**Attack list.**

1. Prove exact flatness, uniqueness, Leibniz iteration, and energy identities.
2. Pin the gauge conjugation to the formalized Hedenmalm conormal prime-jet law.
3. Test against divided-chain recurrence and multiple-zero fibers.
4. Test against the existing cofinal diagonal-inverse no-go: no inverse or bounded Hilbert
   diagonal is to be asserted.
5. External exact-conjunction audit after paper closure.

**Attack result.** The strong scalar reading is false. Let

```text
S_odd(v_+,v_-) = -i(v_+-v_-),       K=ker S_odd=span(1,1),
Gamma_p = diag(+iL_p/2,-iL_p/2).
```

Although `partial_z-Gamma_p` is flat on the marked doublet, it descends through `S_odd` only if
`K` is `Gamma_p`-invariant. But

```text
Gamma_p(1,1)=(+iL_p/2,-iL_p/2) notin K                    (N.9)
```

for every prime. Thus there is no scalar quotient connection making both half-characters parallel.
Using `(N.5)` after scalar soldering silently changes the carrier.

**Verdict.** `[FALSIFIED IN THE SCALAR CARRIER]`.

### Positive survivor — soldering curvature theorem

Put

```text
e_p(z)=h_p(z)_+ + h_p(z)_-,
o_p(z)=-i(h_p(z)_+ - h_p(z)_-)=b_p(z).
```

Direct differentiation gives the exact two-channel system

```text
partial_z (e_p,o_p)^T
  = (L_p/2) [[0,-1],[1,0]] (e_p,o_p)^T.                  (N.10)
```

Hence

```text
partial_z o_p=(L_p/2)e_p,      partial_z e_p=-(L_p/2)o_p. (N.11)
```

The prime-log Jordan cost is the second fundamental form of the nonparallel odd soldering line
inside the flat marked bundle. On the real axis the full marked first-jet energy is

```text
||partial_z h_p||^2=(L_p)^2/(2p),                         (N.12)
```

so the log-square wall `(N.3)` is precisely the cofinal squared norm of this curvature.

#### Paper proof

Differentiate `exp(+/- izL_p/2)`. This gives
`partial_z h_{p,+}=+iL_p h_{p,+}/2` and
`partial_z h_{p,-}=-iL_p h_{p,-}/2`. Adding and taking `-i` times the difference proves
`(N.10)`--`(N.11)`. For real `z`, both exponentials have modulus one, so the two squared component
norms are each `L_p^2/(4p)`, proving `(N.12)`. Summing and applying the already formalized explicit
lower bound

```text
sum_(p<=X) (log p)^2/p >= (log X)^2/2-39log X-25
```

proves `(N.3)`. Finally `(N.9)` is the same calculation on the kernel generator and proves
non-descent. No analytic, divisor, RH, simplicity, or asymptotic premise occurs. `QED`.

### C3 — source-derived marked endpoint doublet

**Frozen conjecture `[N-MARKED-ENDPOINT-DOUBLET-1]`.** Keep the marked doublet through source-normal
completion instead of quotienting to its odd channel. For continuous logarithmic aperture `L>0`,
define the source window

```text
C_L(x)=exp(-L/2) integral_[x-L/2,x+L/2] k(u)du.             (N.13)
```

Its center derivative and covariant width derivative recover both source-defined endpoints:

```text
partial_x C_L
  = exp(-L/2)[k(x+L/2)-k(x-L/2)],

2(partial_L+1/2)C_L
  = exp(-L/2)[k(x+L/2)+k(x-L/2)].                          (N.14)
```

After Fourier transform and source-normal division by `XiC`, `(N.14)` is exactly the marked
even/odd pair. At `L=log p` its squared prime-normal value is

```text
4/p (|cos(z log p/2)|^2+|sin(z log p/2)|^2)
  = 4/p cosh(Im(z) log p),                                 (N.15)
```

independent of the vertical clock `Re(z)`. Covariant Jordan jets remain in this rank-two bundle;
ordinary scalar jets are recovered only by applying the curved soldering afterward.

Write `m_L(z)=exp(-L/2)(exp(+izL/2),exp(-izL/2))`, and let `S_even`, `S_odd` be the
even/odd solderings. Direct theta-source integration gives the dependency-closed factorization

```text
integral E_L(x) exp(izx) dx = S_even(m_L(z)) XiC(z),
integral O_L(x) exp(izx) dx = -i S_odd(m_L(z)) XiC(z).       (N.16)
```

Thus both channels are source-derived, carry exactly the same divisor, and neither introduces an
uncancelled source line. At `L=log p`, `m_L` is literally the prime-normal marked half-character.
Summing `(N.15)` gives the exact clock-free cutoff law

```text
E_end,N(z) = 4 sum_(p<=N) 1/p + 2 E_rad,N(Im(z)/2).         (N.17)
```

Consequently `E_end,N(z)=o(log(N)^2)` if and only if `Im(z)=0`. This is a complete receiver-domain
classification, not a proof that Xi root blocks enter the closed source domain.

The new source-domain target is: prove the endpoint doublet `(N.14)`, not merely its odd interval
quotient, has a closed source-normal Besicovitch landing on the theta Grushin domain before root
specialization. This remains RH-bearing at grade zero. Its advantage is exact multiplicity transport
without an accidental simplicity condition and removal of finite-prime clock recurrence from the
energy itself.

**Attack status.**

1. `[CLOSED]` Prove `(N.13)`--`(N.15)` from actual theta source, including endpoint regularity.
2. `[CLOSED]` Both endpoint channels survive the same source-normal quotient; `(N.16)` proves exact
   common-divisor factorization with no extra source line.
3. `[OPEN HARD CORE]` Test closedness against source-linear superselection: conjecture keeps a direct marked
   doublet and asserts no reflected-sector sewing or diagonal inverse.
4. `[PARTIAL]` Exact finite-cutoff row energy and domain are `(N.17)`; source-derived closed
   all-prime operator estimate before zero specialization remains open.

### C4 — dissipative reflected source inverse

**Conjecture.** Use compact theta-source inverse `B` directly. If `B` is dissipative and source
reflection gives `RBR=-B`, then every eigenvalue `lambda` and `-lambda` lie in the same closed
half-plane, forcing `Im(lambda)=0` without an all-prime row estimate.

**Falsification / corpus collision.** The source Volterra realization has the exact adjoint law

```text
B* + B = rank-two endpoint boundary form,
```

and this rank-two form is indefinite. On a root eigenmode its value is exactly a positive singular
metric factor times `2 Im(lambda)`. Hence one-sided dissipativity is not supplied by source
reflection: it is precisely the missing boundary-charge neutrality, already an RH-equivalent
premise. The rank-two defect has both signs before root specialization, so no unconditional sign
can be extracted from positivity of the source density.

**Pivot.** Any successful Route-N producer must cancel or orient the endpoint flux on
divisor-supported source torsion before pointwise root evaluation. Operator compactness and
reflection symmetry alone cannot do it.

### C5--C6 — fixed/moving theta Hilbert landing

**C5 conjecture.** Put normalized prime translations and endpoint detectors in one fixed theta
Hilbert fibre. **Falsification.** For every nonzero translation `a`, the theta weight ratios

```text
k(x)/k(x+a),  k(x+a)/k(x)
```

are unbounded at opposite ends. No two-sided fixed-fibre comparison exists. Moving translated
fibres make transport isometric but absorb the detector; the fixed fibre retains radial signal but
makes transport unbounded. This is detector/transport metric incompatibility.

**C6 conjecture.** Land endpoints in the canonical source space `H_k=L2(k^-1 dx)`.
**Falsification.** For half-aperture `a>=log(2)/2`,

```text
k(x-a)^2/k(x) -> infinity
```

and is nonintegrable. The exact theta-envelope ratio contains the positive double-exponential
factor

```text
exp(9x/2-9a + pi(1-2 exp(-2a)) exp(2x)).
```

The actual even endpoint, not merely one summand, is outside `H_k`; every prime aperture already
crosses the threshold. Canonical fixed Hilbert landing is mathematically impossible.

### C7--C8 — moving horizon and universal boundary atom

At the moving point `x=-L/2`, the endpoint doublet has exact energy

```text
2 exp(-L) (k(0)^2+k(L)^2).
```

For `L=log p` this is `2/p (k(0)^2+k(log p)^2)`. Hence the cutoff energy splits into

```text
2 k(0)^2 sum_(p<=X) 1/p + summable residual.                (N.18)
```

The residual is dominated by a cubic prime series. Therefore all non-Hilbert mass and radial
selectivity live in one universal boundary atom `k(0)/sqrt(p)`. Quotienting that common atom kills
the detector; retaining it forces the prime-harmonic horizon. Translation-covariant rigging alone
cannot solve RH.

### C9--C10 — Gamma-sewn Fisher source and sharp damping horizon

The universal atom is not externally fitted. The canonical Gamma-sewn Möbius soft source has
prime-grade mass `1/(p log p)`. Multiplication by the square root of its source-generated Julia
prime-log tangent gives exactly `p^-1/2`. Positive damping `u` gives the source-derived marked
energy

```text
p^(-1-u+Im z) + p^(-1-u-Im z).                             (N.19)
```

Consequently its all-prime Hilbert admission law is sharp:

```text
GammaSewnHedenmalmDampedMarkedSummable(u,z)
  <-> |Im z| < u.                                          (N.20)
```

Thus `|Im z|` is the exact abscissa at which the actual Gamma-sewn Fisher source enters Hilbert
space. The RH-bearing producer is now precise: prove every Xi root conormal lands in `(N.20)` for
every `u>0`. Fixed positive aperture is insufficient; all positive damping forces `Im z=0`.

### C11 — Route N / Route R critical-wall identity

At nonzero centered grade `t`, set the Route N damping to its sharp horizon `u=|t|`. Its positive
marked energy is exactly

```text
N_t(p)=p^-1+p^(-1-2|t|).                                  (N.21)
```

The second term is summable. Route R's signed Gamma--Bockstein at its moving first-trace wall is
already known to equal `-sign(t) p^-1` modulo `ell1`. Therefore

```text
N_t = -sign(t) R_t  mod ell1.                              (N.22)
```

This identifies two formerly separate frontier detectors as polarizations of one source boundary
class. It is not an RH proof, but it prevents double-counting these walls.

### C12 — exact Krein-gauge conjugacy

C11 added the two marked channel masses and thereby hid their orientation. Retain instead their
canonical fundamental-symmetry charge. At critical damping, for the actual Gamma-sewn marked
doublet `v_t(p)`,

```text
Q_t(p)=||v_t(p)_+||^2-||v_t(p)_-||^2
      =p^(-|t|)(p^(-t)-p^t)/p.                            (N.23)
```

Let `d(p)=p/(p+1)^2` be the source-selected activation Fisher density. The single
grade-independent gauge

```text
g(p)=p d(p)=p^2/(p+1)^2,       1/4 <= g(p) <= 1           (N.24)
```

has bounded reciprocal and satisfies the exact primewise identity

```text
R_t(p)=g(p) Q_t(p).                                       (N.25)
```

Thus orientation was already present in Route N's two-channel source; positive scalarization lost
it. Multiplication by `g` and by `g^-1` both preserve `ell1`, so `g` induces a canonical
automorphism of the fixed all-prime quotient and carries the Route N Krein class exactly to the
Route R wall class. This is stronger than `(N.22)`: no summable error remains after the canonical
Fisher gauge. In particular `Q_t` is summable exactly at `t=0`; unlike positive horizon energy,
the retained charge is a sharp neutral-grade classifier. Remaining missing operation is not
orientation recovery. It is source-pinned singular base change carrying each actual Xi root
conormal into this marked Krein/Fisher carrier on divisor-supported torsion, before pointwise root
evaluation and for every positive damping.

### C13 — ambient conormal base-change no-go

The literal Fredholm cokernel conormal is `g_z(x)=k(x)exp(-i conjugate(z)x)`. Its weighted squared
mass has the exact source-character form

```text
normSq(g_z(x))/k(x) = |k(x) sourceChar(2z,x)|.             (N.26)
```

Every Xi zero obeys `|Im z|<1/2`, so `(N.26)` is integrable: all actual root conormals already lie
in the ambient weighted theta source space. On this entire conormal strip, however, simultaneous
ambient and Gamma-sewn marked admission is still exactly

```text
|Im z| < u.                                                (N.27)
```

For every fixed `0<u<1/2`, the explicit ambient conormal `z=iu` satisfies `(N.26)` but fails
`(N.27)`. Therefore no total ambient base change can send all weighted theta conormals into the
literal damping-`u` marked fibre; this fails before asking for boundedness or linearity. The open
map cannot live on the completed ambient conormal Hilbert space. It must first localize to the
divisor-supported Fredholm cokernel torsion and only then complete. Restricting `(N.27)` to actual
Xi roots for every `u>0` is formally equivalent to RH, so this categorical relocation identifies
the exact producer site without smuggling in the conclusion.

### C14 — singular modular deconvolution and support exchange

The critical Krein wall retains the full positive transverse modular character, not merely its
prime-harmonic shadow. For every real grade and ordinary prime,

```text
1 + sign(t) p Q_t(p) = p^(-2|t|).                         (N.28)
```

The right side is multiplicative in the positive clock and equals one at one prime exactly when
`t=0`. Away from neutral grade, `(N.28)` uniquely forces the deconvolution coefficient to be `p`.
This coefficient is unbounded. More sharply, it sends the summable witness `p^-2` to the
nonsummable prime-harmonic sequence `p^-1`; therefore it neither preserves `ell1` nor induces a
diagonal map on the fixed all-prime quotient.

Under the bounded Fisher gauge `(N.24)`, Route R needs the uniquely forced coefficient

```text
h(p)=p/g(p)=(p+1)^2/p,
1 + sign(t) h(p) R_t(p)=p^(-2|t|).                        (N.29)
```

It has the same no-quotient obstruction. Thus the bounded part of Route N/Route R comparison is
complete, and the remaining singularity is exactly one prime-clock factor—not an unspecified
topology. On an actual Xi divisor fibre, scalar Cartier atom survival/noncontractibility and
summability of the Route N Krein current have identical support; off line the ordinary scalar
derived fibre contracts precisely while the fixed-trace Krein obstruction survives. This
support exchange is the long-sought Bockstein shadow: modular density must be constructed before
fixed-trace completion on the source-generated exceptional Cartier object.

The conjecture that a bounded Hilbert/Krein correction might realize the required Ward or
transverse-density lift is therefore false. Existing adapted-node four-unit overspend already
rules out even cofinal Hilbert Gram lifts. Canonical finite Wold thermofield vectors and finite
Boolean contractions already exist in the corpus, so reconstructing finite half-densities would
not advance the route. C17 below identifies their source-canonical coupling through exponent parity
and localizes the nonsummable modular class to its squarefree digit. The remaining producer must
carry that singular squarefree source through the exceptional Gamma/Mellin reporter to every Xi
conormal. Pointwise invariance must then make `(N.28)` equal one and force neutral grade;
constructing another receiver, finite packet, or bounded diagonal inverse cannot advance Route N.

### C15 — Kakutani polarization of the Route N critical doublet

At the critical horizon, write the universal and twisted marked-channel masses as

```text
M_0(p)=p^-1,
M_t(p)=p^(-1-2|t|).
```

Their ratio is exactly the transverse modular cocycle:

```text
M_t(p)/M_0(p)=p^(-2|t|).                                 (N.30)
```

The square-root amplitudes are `A_0(p)=p^-1/2` and
`A_t(p)=p^(-1/2-|t|)`. Their squared gap is the existing prime-valuation Hellinger numerator and
is the canonical positive polarization of the signed Route N wall:

```text
H_t(p)=(A_0(p)-A_t(p))^2
      =p Q_t(p)^2/(1+p^-|t|)^2.                          (N.31)
```

Thus the singular factor `p` in C14 is division by the universal critical mass `p^-1`; it is not
an arbitrary diagonal renormalization. The external-looking Kakutani detector and the Route N
Krein wall are two polarizations of one Gamma-sewn source doublet. Summability of `(N.31)` is
equivalent to `t=0`, but this remains a detector until source localization forces the distinguished
Xi conormal into its neutral sector.

### C16 — full Wold thermofield collision

The C15 amplitudes are literally the square roots of the existing critical and twisted Wold
valuation masses, and their product is the existing cross mass

```text
A_0(p)A_t(p)=p^(-1-|t|).
```

Let `F_t(p)` be the existing squared local Wold thermofield Hellinger affinity between critical
and drift `-|t|`. Exact algebra gives

```text
1-F_t(p)
 = H_t(p)/(1-p^(-1-|t|))^2
 = [p Q_t(p)^2/(1+p^-|t|)^2]/(1-p^(-1-|t|))^2.          (N.32)
```

Consequently the complete normalized product-sector defect, not only its numerator, is generated
by the same Route N doublet and the same signed Krein charge. Its prime sum is finite exactly at
`t=0`. This closes the carrier-identification question at every local Wold factor. It does not
prove that a Xi top conormal is the source-derived thermofield class. Remaining work is now
strictly the source-first Boolean--Wold/Cartier localization and modular-marginal conservation
theorem, not construction of finite Wold vectors or a new Kakutani comparison.

### C17 — squarefree parity localization of the singular class

The canonical dyadic exponent split `k=e+2j` couples geometric Wold depth to its Boolean parity
digit. For any nonnegative geometric parameter `q`, parity odds are exactly `q`. Applied to Route
N's critical and twisted masses, this gives

```text
odds_t(p)/odds_0(p)=p^(-2|t|),
odds_t(p)-odds_0(p)=sign(t) Q_t(p).                       (N.33)
```

Thus the transverse modular cocycle and its oriented Krein wall already live on the
source-canonical squarefree digit. The paired-depth residual has odds `q^2`, so its modular ratio
is the square of `(N.33)`, but its twisted-minus-critical all-prime sequence is summable for every
real `t`:

```text
sum_p |p^(-2-4|t|)-p^-2| < infinity.                     (N.34)
```

In contrast, the parity-odds displacement is summable exactly at `t=0`. Hence the fixed-quotient
Route N class is entirely squarefree; the higher dyadic Wold tower is a regular correction. This
closes the generic Boolean--Wold coupling task and relocates the genuine producer to the already
identified squarefree singular source correspondence:

```text
squarefree parity source
  -> exceptional Gamma/Mellin/Cartier reporter
  -> every Xi principal conormal and multiplicity jet.
```

No scalar Boolean entropy normalization enters this map.

### C18 — algebraic Xi conormal landing is already unit-flat

The squarefree Fourier counterface already has the source-defined Mellin reporter

```text
Z_sq(s)=zeta(s)/zeta(2s).
```

On the strict-right half-strip `1/2<Re(s)<1`, the factor

```text
u_sq(s)=zeta(2s)^-1                                      (N.35)
```

is analytic and nonzero. Therefore `Z_sq=zeta*u_sq` has the same zero germ and complete analytic
order as `zeta`; the archimedean factor is also an analytic unit in the open strip, so

```text
ord_s Z_sq = ord_s zeta = ord_s Xi.                      (N.36)
```

This closes algebraic principal-conormal and full multiplicity landing for every strict-right Xi
point. It is a consolidation of existing squarefree fixed-current and Xi-order theorems, not a new
divisor mechanism. The frozen open phrase “attach every Xi conormal” was too broad: attachment as
an analytic germ is already complete. What remains is proving that this germ survives and is
normal/nonexpansive in the strict critical Fourier--Mellin/Cartier topology while retaining the
parity modular marginal `(N.33)`. Analytic-unit equality alone does not supply that topology.

### C19 — the parity wall is literal projective Weyl leakage

The Gamma-sewn grade canonically selects the residue-projective marked weight

```text
z_t(p)=-|t| log p,       exp(2z_t(p))=p^(-2|t|).          (N.37)
```

On `P^1(F_p)`, the marked-to-bulk odds of the projective natural-cone vector are
`exp(2z)/p`. Therefore the selected state has odds `p^(-1-2|t|)`, exactly the twisted
squarefree-parity odds from `(N.33)`. At `t=0` it is the uniform projective source vector and is
fixed by residue Weyl inversion.

For the foreign producer/reporter polarization, exact compression leakage is

```text
L_t(p)=H_t(p) (p-1)/(p+p^(-2|t|)).                       (N.38)
```

Since `p>=2` and `0<p^(-|t|)<=1`,

```text
(1/3) H_t(p) <= L_t(p) <= H_t(p),
sum_p L_t(p)<infinity  iff  t=0.                         (N.39)
```

Thus Route N's Kakutani wall is not only asymptotic to projective leakage: it is a uniformly
equivalent literal residue-clock Weyl leakage. This closes the finite projective realization and
the all-prime sector classifier.

It also falsifies the naive scalar-normality reading of the remaining gate. Off neutral grade,
the scalar projective/Fock completion deletes the germ by an orthogonality catastrophe; declaring
that every Xi germ stays in the same scalar sector would simply assume the desired grade. A valid
producer must first construct the complementary continuation--record correspondence and then prove,
from the source Fourier--Mellin relation, that Xi principal conormals have zero record component.
Normality by itself is no longer an admissible unexplained premise.

### C20 — every Route N reporter is one Kadison fracture

Let the projective multiplicative-domain defect be

```text
D_t(p)=1-p^(-2|t|).                                      (N.40)
```

The C14 deconvolution and C15/C19 polarizations now give one exact dictionary:

```text
D_t(p)=-sign(t) p Q_t(p),
H_t(p)=D_t(p)^2/[p(1+p^(-|t|))^2],                       (N.41)
L_t(p)=D_t(p)^2(p-1)/
       [p(1+p^(-|t|))^2(p+p^(-2|t|))].                  (N.42)
```

Moreover the logarithmic record density recovers the complete absolute grade:

```text
log(1-D_t(p))/(2 log p)=-|t|.                            (N.43)
```

Thus the signed Krein wall is the oriented linear fracture, the Kakutani numerator is its
normalized quadratic polarization, and literal projective Weyl leakage is its residue-compressed
quadratic polarization. Wold thermofield defect is the same quadratic numerator with the existing
geometric denominator `(N.32)`. These are not independent constraints capable of forcing one
another to vanish.

This is the higher universal principle exposed by the repeated failures: positive completion sends
source inverse transport to an adjoint transport and stores their mismatch as `D_t`; every Route N
metric is a functorial shadow of that conserved mismatch. Remaining arithmetic theorem is therefore
not another norm, sector, or record construction. It must prove, before divisor specialization,
that functional-equation duality and positive Fourier--Mellin adjunction are the same transport on
the source-landed squarefree Xi principal conormal. Then `(N.40)` vanishes and `(N.43)` forces
`t=0`.

### C21 — zero fracture on Xi conormals is exactly the RH receiver

For an actual Xi divisor copy `q`, set its Route N radial grade and local defect to

```text
t(q)=Re(q)-1/2,
D_Xi(q,p)=D_(t(q))(p).                                  (N.44)
```

The C20 purity classifier gives, for every fixed ordinary prime `p`,

```text
D_Xi(q,p)=0  iff  Re(q)=1/2,
[for all q, D_Xi(q,p)=0]  iff  RH.                      (N.45)
```

Every strict-right squarefree Xi zero germ from C18 instead has `D_Xi(q,p)>0` at every prime.
Thus algebraic germ attachment, projective realization, complete positivity, or continuation by
functional-equation reflection cannot supply the missing vanishing. Functional equation permits a
free reflected off-line pair and exchanges its two conormals; it does not fix either member or
identify inverse transport with positive adjunction on it.

This collides exactly with the retired
`XI_INTERNAL_REFLECTION_RANK_NONCREATION` premise in
`faithful-reflection-tate-conormal-localization-rh.md`: zero complementary record, same-sector
normality, multiplicative-domain purity, and duality--adjunction equality are different names for
the same RH receiver after divisor specialization. Treating any as a source theorem would be
circular.

**Terminal verdict.** Route N has no independent source producer below `(N.45)`. Its strongest
positive survivor is the exact C19--C20 projective/fracture dictionary: all Route N walls are
functorial polarizations of one conserved duality--adjunction mismatch. Successor work must enter
through an independent pre-divisor incidence or annihilator—currently the source-conditioned
Mobius multiplication-graph curvature—not through another Route N reporter.

### C22--C23 — projective fracture is reciprocal Sonin conormal escape

The terminal verdict does not mean the fracture disappears under completion. Define the
inward-oriented Sonin ladder character and its complementary escape amplification by

```text
lambda_in(t,p)=p^(-|t|),
A_t(p)=|lambda_in(t,p)|^(-2)=p^(2|t|).                 (N.46)
```

Then the C20 projective survival and Sonin escape obey the exact conservation and odds laws

```text
|lambda_in(t,p)|^2=1-D_t(p),
(1-D_t(p)) A_t(p)=1,
D_t(p)/(1-D_t(p))=A_t(p)-1,                            (N.47)
log A_t(p)/(2 log p)=|t|.                              (N.48)
```

This is more than a scalar collision. For an actual zeta zero `w` in the strict-right strip, the
full closed co-Poisson source is annihilated at every aperture, so its quotient kernels `y_j` obey

```text
||y_j||^2 <= (1-D_(Re(w)-1/2)(p)) ||y_(j+1)||^2.       (N.49)
```

Since the initial evaluation vector is nonzero and the outward Sonin character has norm strictly
above one, `||y_j|| -> infinity` along every aperture ladder of ratio `r>1`. Thus positive
projective completion does not erase off-line fracture: it transfers it exactly into divergent
complementary co-Poisson conormal mass. This is the higher conservation principle behind C19--C21.

**No-go refinement.** Requiring the completed conormal ladder to stay uniformly bounded would
force RH and is another receiver. Viable successor cannot demand zero record or bounded escape;
it must use an independent source identity that cancels or orients the escaping corona charge
before divisor specialization. Literal Fisher-numerator divisibility is also rejected: at a zero
of order `d`, overlap has order `d` and its derivative numerator order `d-1`, so the residue is the
nonzero conormal record that must be retained.

### C24--C25 — flat connection and Route N--Route R hyperbolic mass shell

A curvature pivot fails for a precise reason. The two co-Poisson bonding paths already commute on
the entire quotient, before zero specialization. Reflection exchanges the reciprocal edges, so
their oriented determinant character cancels on the diagonal. What survives is Hermitian
nonmetricity, not connection curvature. Define

```text
M_t(p)=D_t(p)^2/(1-D_t(p))
      =A_t(p)+A_t(p)^(-1)-2.                            (N.50)
```

Then `M_t(p)>=0`, it is invariant under `t -> -t`, and it vanishes exactly at `t=0`. On every
actual strict-right zero, the literal forward and inverse co-Poisson edge images obey, at every
aperture level,

```text
||T^+ y_(j+1)||^2+||T^- y_(j+1)||^2
  =(2+M_(Re(w)-1/2)(p))||y_j||^2.                       (N.51)
```

At an initial aperture below one the evaluation vector is nonzero, so the left side is strictly
larger than `2||y_0||^2`. Thus flatness and metric compatibility are independent; asking for the
balanced value `2` on every zero fibre is another RH receiver.

The signed Burnol finite-holonomy wall supplies the complementary coordinate. For prime dilation
ratio and any actual strict-right zero, its normalized value is

```text
H=A_t(p)-A_t(p)^(-1)
 =D_t(p)(2-D_t(p))/(1-D_t(p)),                           (N.52)
H^2=M_t(p)(M_t(p)+4).                                   (N.53)
```

Hence Route N's positive projective fracture and Route R's oriented Burnol holonomy lie on one
hyperbolic mass shell. Reflection reverses `H` while preserving `M`; it cannot annihilate either.
The two routes do not provide independent inequalities that can be combined. The only remaining
producer must enter before reciprocal flat transport, through source incidence/current structure
that is not determinant-one reflection data.

### C26--C27 — Fisher ideal failure and affine conormal residue conservation

The source-incidence pivot has a sharp ideal-theoretic answer. For any base point
`Re(sigma)>1`, nonzero affine direction `epsilon`, and coordinate `u` meeting a strict-right Xi
zero `rho=sigma+u epsilon`, put

```text
B(u)=Z_sq(sigma+u epsilon)/Z_sq(sigma),
F(u)=2(B'(u)+epsilon A_sq(sigma)B(u)).                  (N.54)
```

If the Xi multiplicity at `rho` is `m>=1`, then the complete local laws are

```text
ord_u(B)=m,
ord_u(F)=m-1,
not exists analytic q with F=Bq,
lim_(v->u, v!=u) (v-u)F(v)/B(v)=2m.                    (N.55)
```

Thus the proposed charged-graph divisibility gate is mathematically impossible, including at
multiple zeros. The derivative does not land in the overlap ideal; it lands in the one-dimensional
conormal quotient. Its exact positive survivor is the nonzero residue `2m`.

This residue is not separate from the completed source normal cone. Multiplying it by the uniquely
reflection-compatible centered affine polarization gives

```text
[-(rho-1/2)/2] * [2m] = -(rho-1/2)m,                   (N.56)
```

exactly the residue of the exceptional Xi affine divisor current. Its real part is strictly
negative for every strict-right zero. Hence Fisher conormal, exceptional normal cone, and Xi
position-times-multiplicity current are one conserved source incidence. This supplies the
independent oriented coordinate missing from Route N's reflection-even reporters, but it still
records rather than eliminates the divisor.

**Producer relocation.** Remaining RH-producing theorem must be upstream: derive from pre-divisor
Euler--Gamma--Stokes structure a sign or annihilation law excluding negative horizontal affine
source residue. Divisibility, reciprocal curvature, bounded escape, or another Route N/R reporter
cannot do this. Forcing residue to vanish would erase critical-line multiplicity as well and is
not an admissible substitute.

### C28 — Route N reciprocal charge is Route T timelike boost charge

The affine-residue handoff admits an exact pre-divisor reinterpretation in the mass propagator.
For Route T real phase

```text
Theta_(a,u,h)(x) = u sqrt(x^2+a^2) + h x,             (N.57)
```

put `q=sqrt(u^2-h^2)`. If `a>0` and `0<=h<u`, then

```text
x_* = -a h/q,
Theta'(x_*)=0,
sqrt(x_*^2+a^2)=a u/q,
Theta(x_*)=a q,                                        (N.58)
```

and `x_*` is the unique stationary point. If `0<u<=h`, then `Theta'(x)>0` for every real `x`;
the source frequency is spacelike and has no saddle. These statements are exact, not asymptotic
stationary phase.

For any reciprocal amplification `A>1`, define

```text
u_A=(A+A^(-1))/2,
h_A=(A-A^(-1))/2.                                     (N.59)
```

Then `0<h_A<u_A`, `sqrt(u_A^2-h_A^2)=1`, and the Route T boost coordinates are

```text
H_T=2h_A=A-A^(-1),
M_T=2u_A-2=A+A^(-1)-2,
H_T^2=M_T(M_T+4).                                      (N.60)
```

Taking `A=A_t(p)`, the Route N Sonin escape amplification, identifies `M_T` with the C24 Route N
Hermitian nonmetricity. At every actual strict-right zeta zero it identifies `H_T` with the C25
normalized Burnol holonomy. Hence the canonical Route T saddle is

```text
x_* = -(a/2) H_Burnol,                                 (N.61)
```

while its phase is the unit-proper-time value `a`.

C27's divisor coordinate is the logarithmic, rather than linear, boost coordinate. For Xi
multiplicity `m` at a strict-right `rho`, every prime `p` gives

```text
Re[-(rho-1/2)m]
  = -m log(A_(Re rho-1/2)(p))/(2 log p).                (N.62)
```

Thus Fisher conormal residue, affine Xi current, Sonin escape, Burnol holonomy, Route N
nonmetricity, and Route T stationary mass ray are one conserved boost charge in residue,
rapidity, orientation, energy, and saddle coordinates. This is the higher universal principle
behind the repeated no-gos: downstream completion changes coordinate but cannot create a second
inequality. A valid producer must control arithmetic injection of this boost charge before the
divisor/reciprocal transport forms.

### C29 — boost handoff determines exact spacelike contour rate

The Route T side of C28 exposes a quantitative survivor unavailable to Route N's downstream
reporters. With damping `sigma>0` and spacelike frequency `0<u<h`, define

```text
zeta=(sigma+i*u)^2+h^2,
kappa=Re sqrt(zeta).                                    (N.63)
```

After the mass substitution `x=a sinh t`, a curved contour with nonnegative angle coordinates
`c^2+s^2=1` has squared damping rate

```text
lambda(c,s)^2=(sigma*c+h*s)^2-(u*s)^2.                 (N.64)
```

`RHTower.XiMassSpacelikeContourOptimality` proves the exact attained variational law

```text
max lambda(c,s)^2 = kappa^2,                           (N.65)
h-u < sqrt(h^2-u^2) < kappa.                           (N.66)
```

The optimizer is lifted in Lean to actual nonnegative contour coordinates. At vanishing damping,
balancing critical coefficient growth against the resulting Lorentz rate yields

```text
alpha_sharp(a)=a/sqrt(a^2-1/4)
  < a/(a-1/2)=alpha_horizontal(a),                     (N.67)
```

for every legal `a>1/2`; Lean also proves the exact inequality equivalence defining this threshold.
This is a real cross-route gain: C28's boost is not only a dictionary but identifies strict loss in
Route T's horizontal-strip cone. It still is not an RH producer. Required analytic lift is the
full-exponent curved-contour/Bessel bound for the mass Fourier transform, followed by arithmetic
control of the residual timelike-plus-glancing cone.

### C30--C32 — branch-free transform and exact optimal Bessel lift

C30 removes the square-root branch from the Fourier carrier by the exact full-line substitution

```text
F_(sigma,u)(h)
 = int_R a cosh(t) exp(-(sigma+i*u)a cosh(t))
       exp(-i*h*a*sinh(t)) dt.                         (N.68)
```

The transformed kernel is entire. C31 proves a genuinely one-sided contour deformation
`t -> t-i*theta` for every `0<=theta<pi/2`. Put

```text
A=sigma*cos(theta)+h*sin(theta),
B=u*sin(theta),
q=sqrt(A^2-B^2),
r=arsinh(B/q).
```

The exact Lorentz identity and Schlaefli bound are

```text
A cosh(t)+B sinh(t)=q cosh(t+r),                       (N.69)
|F_(sigma,u)(h)| <= 2*a*exp(r)*K_1(a*q),              (N.70)
K_1(s) <= exp(-(s-s0))*K_1(s0),  0<s0<=s.             (N.71)
```

C32 proves C29's maximizing nonnegative contour is an actual interior angle and therefore inserts
the optimum without a limiting or compactness gap:

```text
q = Re sqrt((sigma+i*u)^2+h^2)=kappa.                 (N.72)
```

Consequently `(N.70)` holds at exact exponent `a*kappa`, while `(N.71)` retains exponential
coefficient `1` relative to any fixed positive base rate. This closes the complete positive
analytic survivor exposed by Route N's failure. It still does not revive Route N: remaining
obstruction is Route T's source-level centered von Mangoldt cancellation in residual
timelike-plus-glancing cone.

### C33 — uniform boost control and sharp-spacelike atom summability

C32 alone did not justify summing the optimal atom bounds: optimizer-dependent `exp(r)` remained.
C33 closes that gap. In every strict slope cone `alpha*u<=h`, `alpha>1`, optimal Lorentz coordinates
satisfy `alpha*B<=A`, hence

```text
exp(r)<= (alpha+1)/(alpha-1).                         (N.73)
```

For `alpha>alpha_sharp(a)`, Lean proves

```text
p(a,alpha)=1/2+a*sqrt(1-alpha^-2)>1,                 (N.74)
|exp(-h/2)F_u(h)|<=C(a,alpha)exp(-p(a,alpha)h).       (N.75)
```

Thus all centered atoms with `alpha*u<=log n` are absolutely dominated by
`C(a,alpha)(Lambda(n)+1)n^-p`. Both Dirichlet series converge. The full finite cone is proved
exactly equal to this uniformly bounded sharp-spacelike sum plus complementary finite sum
`log n<alpha*u`; no atom or boundary term is lost. This is the complete positive Route N-to-T
survivor. Remaining obstruction is now literally the complementary source sum, not an analytic
contour debt.

### C34 — residual localization reaches every strict causal enlargement

C33 initially leaves the restriction `alpha>alpha_sharp(a)`. C34 proves this creates no fixed
angular loss. For every `alpha>1`, choose

```text
a=alpha/sqrt(alpha^2-1)>1/2;                         (N.76)
```

then Lean proves `alpha_sharp(a)<alpha`. Adding and subtracting C33's uniformly bounded
sharp-spacelike part gives the exact criterion

```text
RH iff the centered residual sum on log n<alpha*u
       is uniformly bounded for u>=0.                (N.77)
```

for suitable legal Route T parameters and every `sigma>0`. Thus all analytically easy spacelike
directions can be removed with slope arbitrarily close to `1`. The unresolved class is intrinsic
to causal timelike-plus-glancing incidence, not to a suboptimal contour or mass choice.

## Collision and novelty boundary

- Marked half-character, root torsor, odd soldering, reflected radial energy, and diagonal-inverse
  obstruction: corpus-owned; no novelty claimed.
- Prime-log moment asymptotics and multiplicative-regularization blindness: corpus-owned; no novelty
  claimed.
- Hedenmalm divided Jordan chain and symmetric-carrier simplicity obstruction: corpus-owned and
  explicitly classified as a non-new bridge.
- Candidate delta: exact non-descent/soldering-curvature law `(N.9)`--`(N.12)`, source-window
  endpoint factorization `(N.13)`--`(N.16)`, and clock-free cutoff decomposition/classification
  `(N.17)`, exact Route-N/Route-R Krein-gauge conjugacy `(N.23)`--`(N.25)`, and unique singular
  recovery of the transverse modular cocycle `(N.28)`--`(N.29)`, together with its exact channel
  Radon--Nikodym, Kakutani-polarization, and full Wold-thermofield forms `(N.30)`--`(N.32)`, and
  squarefree parity localization with summable residual tower `(N.33)`--`(N.34)`.
  The projective weight/odds collision and exact uniformly equivalent Weyl leakage
  `(N.37)`--`(N.39)`, plus the complete projective/Kadison fracture dictionary
  `(N.40)`--`(N.43)`, are the C19--C20 candidate delta. C21's exact Xi/RH receiver classification
  `(N.44)`--`(N.45)` is the dependency-closed no-go boundary, not evidence for RH. C22--C23 add
  the exact projective-survival/Sonin-escape conservation and actual-zero corona divergence
  `(N.46)`--`(N.49)` as a further positive survivor. C24--C25 add the flat-but-nonmetric trace
  law `(N.50)`--`(N.51)` and exact Route N--Route R hyperbolic mass shell `(N.52)`--`(N.53)`;
  these are a positive cross-route classification and prove that the two walls are not independent.
  C26--C27 add the exact squarefree Fisher conormal order/residue law `(N.54)`--`(N.55)` and its
  equality with the exceptional Xi affine-current residue `(N.56)`. C28 adds the exact timelike
  stationary classification `(N.57)`--`(N.58)`, reciprocal embedding and mass shell
  `(N.59)`--`(N.60)`, actual-zero Burnol saddle `(N.61)`, and affine-residue/rapidity law `(N.62)`.
  C29 adds the attained optimal spacelike contour law `(N.63)`--`(N.66)` and strict sharp-cone
  improvement `(N.67)` on the Route T side of the handoff. C30--C32 add exact branch-free
  hyperbolic representation `(N.68)`, one-sided deformation/Lorentz/Bessel laws
  `(N.69)`--`(N.71)`, and exact optimizer insertion `(N.72)`.
  Generic order-drop, logarithmic-residue, and Lorentz-rapidity principles are classical/corpus-owned;
  the candidate delta is their exact source-defined Route N Fisher/Sonin/Burnol to Route T mass-ray
  synthesis, not any generic constituent theorem.
  The algebraic squarefree-to-Xi conormal unit bridge `(N.35)`--`(N.36)` is corpus consolidation,
  not part of the novelty claim.
  Ordinary prime-normal prolongation is not a removable
  artefact inside the scalar carrier; its log cost measures failure of the flat marked connection
  to descend.
- Current primary-literature search found Hedenmalm's June 2026 spectral paper, his March 2026
  Klein--Gordon Liouville paper, Bakan--Hedenmalm--Montes-Rodriguez's hyperbolic Fourier framework,
  and Burnol's Hankel-causality/Sonine work. These own generic causal, Lorentz, Hankel, and Bessel
  ancestry, but no prime-normal, prime-log-Jordan, Gamma-sewn Fisher provenance, or exact Route N
  boost-to-centered-von-Mangoldt optimal-contour conjunction was located. External novelty remains
  provisional.

## Hostile scope

1. Flat marked transport does not prove `(N.8)` or the new endpoint-doublet landing.
2. It does not create a positive form, bounded diagonal inverse, or ordinary-`L2` completion.
3. It does not prove Xi zeros simple; it removes an accidental simplicity demand from the RH lane.
4. It does not evade the generic-source falsifier. Generic positive sources with nonreal Fourier
   zeros must still fail grade-zero descent.
5. It does not replace the source-normal nonsummable topology by a summable Hilbert row.
6. Divisor localization alone is insufficient: ordinary scalar derived specialization is
   contractible off neutral grade. The needed object is strict boundary-heart/transverse-density
   base change, not ordinary derived scalar base change.

## Gates

- [x] 0 -> 1: exact source-pure statement frozen; collisions and falsifiers recorded
- [x] 1 -> 2: C21 proves proposed duality--adjunction/zero-record premise is exactly RH and collides
  with the retired reflection-rank-noncreation route; Route N source mechanism retired
- [x] 2 -> 3: dependency-closed C19--C21 positive survivor/no-go formalized and umbrella-wired;
  direct Lean and focused axiom audits pass
- [ ] 3 -> 4: only if C19--C20 scientific novelty/significance survives hostile external review;
  this cannot reactivate Route N as an RH producer

## No-go closure for C1

- **Exact killing mechanism:** ordinary differentiation of the marked prime character contributes
  `(log p)^2/(2p)` at first grade, whose finite-prime sum has an unconditional log-square lower
  bound.
- **Strongest positive survivor:** canonical flat connection `(N.1)` makes the character parallel
  and moves the complete Jordan filtration into coefficient jets, preserving prime-harmonic rather
  than prime-log energy at every grade.
- **New insight:** Route N has two independent obligations—horizontal grade-zero admission and
  multiplicity transport. Conflating them creates a false simplicity-strengthened frontier.
- **Status:** first-jet obstruction, marked parallelism, connection coupling, and clock-free endpoint
  receiver are Lean-closed. Full iterated covariant-tower theorem remains open, but scalar
  connection descent is retired and no longer an admissible Route-N premise.

## No-go closure for scalar C2

- **Exact killing mechanism:** odd soldering kernel is not invariant under the marked flat
  connection; therefore connection does not descend to scalar prime-normal quotient.
- **Strongest positive survivor:** exact soldering-curvature system `(N.10)` and source-derived
  center/width endpoint doublet `(N.13)`--`(N.14)`.
- **New insight:** log-square Jordan wall is geometric curvature of scalarization, not loose
  arithmetic. Correct full-multiplicity carrier must remain marked until after covariant jets.
- **Status:** soldering-curvature and source endpoint factorization/classification are paper-proved,
  dependency-closed, and formalized in Lean. Endpoint-doublet closed all-prime landing remains
  conjectural.

## No-go closure for C4

- **Exact killing mechanism:** source inverse's adjoint defect is an indefinite rank-two endpoint
  flux. On root modes its quadratic charge is proportional to `Im(lambda)`; dissipativity would
  assume the desired vanishing rather than produce it.
- **Strongest positive survivor:** nonreal spectral displacement is exactly endpoint flux, so a
  valid producer must enforce source-level flux cancellation/orientation before zero
  specialization.
- **Status:** exact adjoint-defect and root-flux identities are already Lean-closed in corpus; C4
  contributes a new route-level exclusion, not a new theorem declaration.

## Lean status

- `HedenmalmPrimeNormalSolderingCurvature.lean`: ordinary first-jet log-square obstruction,
  connection non-descent, even/odd coupling, and exact marked energy.
- `HedenmalmContinuousApertureEndpointDoublet.lean`: source aperture derivatives, common-`XiC`
  endpoint factorization, exact prime restriction, and source-derived endpoint energy.
- `HedenmalmPrimeEndpointDoubletSubLogSquareClassification.lean`: `(N.17)`, harmonic upper bound,
  exact `o(log^2)` domain classification, and RH consumer with visibly open zero-domain premise.
- `HedenmalmThetaTranslationWeightNoGo.lean`: fixed/moving theta-fibre metric incompatibility.
- `HedenmalmThetaEndpointSourceDomainNoGo.lean`: canonical `H_k` endpoint nonintegrability.
- `HedenmalmThetaMovingHorizonBoundary.lean`: exact moving-horizon atom and summable residual.
- `HedenmalmGammaSewnFisherHalfDensityBridge.lean`: literal Fisher source provenance and sharp
  damping horizon `(N.20)`.
- `HedenmalmGammaSewnRouteRCriticalWallBridge.lean`: essential-class identity `(N.21)--(N.22)`.
- `HedenmalmGammaSewnRouteRKreinGaugeBridge.lean`: exact Krein charge `(N.23)`, bounded invertible
  Fisher gauge `(N.24)`, exact Route-R conjugacy `(N.25)`, sharp charge summability, and quotient
  automorphism.
- `HedenmalmGammaSewnCokernelBaseChangeNoGo.lean`: weighted conormal identity `(N.26)`, automatic
  Xi-root conormal admission, sharp joint horizon `(N.27)`, total ambient landing no-go, and exact
  root-only landing/RH equivalence.
- `HedenmalmGammaSewnTransverseModularCocycle.lean`: multiplicative transverse cocycle `(N.28)`,
  pointwise-unique Route N/Route R deconvolutions `(N.29)`, explicit `p^-2 -> p^-1` obstruction,
  no fixed-quotient map, scalar-Cartier/Krein support exchange, and Xi-support/RH endpoint.
- `HedenmalmGammaSewnKakutaniPolarizationBridge.lean`: channel mass ratio `(N.30)`, exact amplitude
  gap/Krein polarization `(N.31)`, and sharp prime-summability classifier.
- `HedenmalmGammaSewnWoldThermofieldBridge.lean`: exact collision with existing critical, twisted,
  and cross Wold masses; full thermofield defect identity `(N.32)` and sharp summability theorem.
- `HedenmalmGammaSewnSquarefreeParityLocalization.lean`: parity-odds cocycle and oriented Krein
  identity `(N.33)`, summable paired-depth residual `(N.34)`, and sharp parity summability theorem.
- `HedenmalmGammaSewnSquarefreeXiConormalBridge.lean`: analytic reporter unit `(N.35)`, exact
  squarefree/zeta/Xi zero-germ and multiplicity equality `(N.36)` on the strict-right strip.
- `HedenmalmGammaSewnProjectiveParityLeakageBridge.lean`: canonical projective weight and exact
  parity-odds collision `(N.37)`, Weyl-fixed neutral state, exact leakage polarization `(N.38)`,
  universal comparison and sharp all-prime classifier `(N.39)`.
- `HedenmalmGammaSewnProjectiveKadisonFracture.lean`: exact oriented linear and normalized
  quadratic fracture laws `(N.40)`--`(N.42)`, purity classifier, and exact logarithmic grade
  recovery `(N.43)`.
- `HedenmalmGammaSewnXiKadisonReceiverNoGo.lean`: actual-Xi radial grade `(N.44)`, pointwise
  zero-fracture/critical-line equivalence, fixed-prime all-conormal/RH equivalence `(N.45)`, and
  strict positivity on every hypothetical strict-right squarefree Xi zero germ.
- `HedenmalmGammaSewnSoninEscapeConservation.lean`: inward Sonin survival `(N.46)`, exact
  defect--escape conservation/odds/log-grade laws `(N.47)`--`(N.48)`, actual-zero
  defect-weighted ladder growth `(N.49)`, and divergence of every strict-right co-Poisson
  conormal ladder.
- `HedenmalmGammaSewnSoninHermitianNonmetricity.lean`: nonnegative reflection-invariant
  Hermitian trace excess `(N.50)`, exact paired-character and literal paired-edge energy
  `(N.51)`, and strict metric incompatibility on every actual strict-right zero.
- `HedenmalmGammaSewnBurnolHolonomyMassShell.lean`: normalized zero-fibre Burnol holonomy as
  escape-minus-inverse-escape and as the rational Kadison coordinate `(N.52)`, plus the exact
  Route N--Route R mass shell `(N.53)`.
- `HedenmalmGammaSewnSquarefreeFisherConormalResidue.lean`: affine squarefree/Xi divisor landing,
  exact Fisher order drop, impossibility of analytic overlap divisibility, and conormal residue
  `2m` `(N.54)`--`(N.55)`.
- `HedenmalmGammaSewnSquarefreeFisherAffineResidueBridge.lean`: exact equality of scaled Fisher
  conormal and exceptional Xi affine-current residues `(N.56)`, plus strict negative horizontal
  sign at every strict-right zero.
- `HedenmalmGammaSewnXiMassTimelikeBoostBridge.lean`: exact timelike/spacelike stationary
  classification `(N.57)`--`(N.58)`, reciprocal Route N embedding and mass shell
  `(N.59)`--`(N.60)`, actual-zero Burnol saddle `(N.61)`, and affine-residue/rapidity identity
  `(N.62)`.
- `XiMassSpacelikeContourOptimality.lean`: exact principal-root/curved-contour variational law,
  actual nonnegative optimizer, strict null-gap improvement, and sharp critical slope
  `(N.63)`--`(N.67)`.
- `XiMassHyperbolicFourierRepresentation.lean`: exact branch-free full-line hyperbolic transform
  `(N.68)` with all substitution and integrability obligations closed.
- `XiMassHyperbolicCurvedContourDecay.lean`: entire extension, one-sided contour equality, exact
  Lorentz translation, order-one Schlaefli bound, and full-exponent Bessel comparison
  `(N.69)`--`(N.71)`.
- `XiMassOptimalCurvedBesselDecay.lean`: interior-angle realization of C29 optimizer, exact
  `q=kappa` insertion `(N.72)`, and optimal/fixed-base full-exponent Fourier bounds.
- `XiMassSharpSpacelikeConeSummability.lean`: uniform optimal-boost law `(N.73)`, strict exponent
  margin `(N.74)`, coefficient-faithful profile bound `(N.75)`, centered-atom absolute summability,
  exact finite cone partition, and cutoff-independent sharp-spacelike bound.
- `XiMassTimelikeGlancingResidualCriterion.lean`: full-versus-residual boundedness equivalence,
  construction of a legal mass parameter for every `alpha>1`, and exact RH criterion `(N.76)`--
  `(N.77)` on arbitrarily sharp residual cones.
- All modules are umbrella-wired. Direct `lake env lean` checks pass through C34. Headline C15--C34
  axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. Final umbrella
  build, lint, and axiom audit remain gate work.

## Log

- 2026-08-09 — card created after C0 collision and C1 falsification; C2 frozen.
- 2026-08-09 — C2 scalar reading falsified by connection non-descent; curvature survivor
  paper-proved; C3 marked source-endpoint doublet frozen.
- 2026-08-09 — C3 attacks 1--2 closed: both endpoint transforms factor through exact same `XiC`;
  prime endpoint energy has clock-free decomposition `(N.17)` and exact Lean domain classifier.
- 2026-08-09 — C4 dissipative/reflection inverse killed by indefinite rank-two adjoint defect;
  remaining open core isolated to source-level all-prime endpoint landing/flux cancellation.
- 2026-08-10 — C14 killed bounded/cofinal Hilbert recovery and proved the uniquely forced
  singular prime deconvolution `(N.28)--(N.29)`. Route N's Krein wall is the fixed-trace shadow of
  the transverse modular cocycle; producer relocated to finite-packet invariant density plus
  strict exceptional-Cartier cofinal passage.
- 2026-08-10 — C15--C16 proved the transverse cocycle is the literal channel mass ratio, its
  Hellinger numerator is the normalized Krein polarization `(N.31)`, and the complete Wold
  thermofield defect is `(N.32)`. Existing finite Wold/Boolean carriers are sufficient; open core
  is their source-canonical coupled strict Cartier totalization and Xi modular-marginal landing.
- 2026-08-10 — C17 proved the source dyadic parity odds carry the entire cocycle and signed Krein
  wall `(N.33)`, while the paired-depth residual is always summable `(N.34)`. Generic
  Boolean--Wold coupling is no longer open; producer narrowed to squarefree singular
  exceptional-reporter landing of every Xi principal conormal and multiplicity jet.
- 2026-08-10 — C18 collided the alleged algebraic conormal-landing gap with existing divisor
  theorems: `Z_sq=zeta/zeta(2s)` differs from zeta and Xi by analytic units on the strict-right
  strip, preserving full order `(N.35)--(N.36)`. Remaining producer is only strict exceptional
  normality/complete nonexpansivity and conservation of the parity modular marginal.
- 2026-08-10 — C19 identified the Gamma-sewn grade with the exact projective marked weight
  `(N.37)`, the twisted parity law with projective marked odds, and the Kakutani numerator with
  uniformly equivalent Weyl leakage `(N.38)--(N.39)`. This closes finite projective realization but
  kills naive same-sector normality: off-neutral germs require a complementary record, so the live
  theorem is source-forced vanishing of that record, not unexplained scalar normality.
- 2026-08-10 — C20 proved Route N's Krein, Kakutani, Wold, and projective reporters are exact
  linear/quadratic polarizations of one Kadison defect `(N.40)--(N.43)`. The obstacle is now a
  single source naturality equation: duality must equal adjunction on the pre-divisor squarefree Xi
  conormal. No further scalar reporter can supply that equality.
- 2026-08-10 — C21 proved zero Kadison fracture at every Xi conormal, at any fixed prime, is
  equivalent to RH `(N.44)--(N.45)`; every hypothetical strict-right squarefree Xi germ has positive
  record. The final premise collides with the already failed internal-reflection rank-noncreation
  route. Route N is terminalized; C19--C20 retained as its exact positive survivor, and research
  pivots to independent Mobius incidence multiplication-graph curvature.
- 2026-08-10 — C22--C23 identified projective survival with squared inward Sonin character and
  proved reciprocal defect--escape conservation `(N.46)`--`(N.48)`. At every actual strict-right
  zeta zero the same survival weights one-step co-Poisson conormal growth `(N.49)`, and the full
  ladder norm diverges to infinity. Completion relocates Route N fracture into complementary
  corona escape; it does not annihilate it. Lean module is umbrella-wired and axiom-clean modulo
  standard quotient/classical axioms.
- 2026-08-10 — C24 disproved the mixed-curvature pivot: the quotient connection is already flat
  on the full co-Poisson quotient, while its reciprocal edge pair has positive Hermitian trace
  excess `M=D^2/(1-D)=A+A^(-1)-2`. Literal paired-edge energy is `(2+M)||y_j||^2` and is
  strictly unbalanced on every actual strict-right zero.
- 2026-08-10 — C25 proved normalized Burnol holonomy is the oriented coordinate
  `H=A-A^(-1)=D(2-D)/(1-D)` and satisfies `H^2=M(M+4)`. Route N and Route R walls are exact
  trace/orientation polarizations of one hyperbolic mass shell, so their conjunction supplies no
  independent pressure. Both modules are umbrella-wired and axiom-clean modulo standard
  quotient/classical axioms.
- 2026-08-10 — C26 disproved the live source card's Fisher-divisibility gate at every actual
  strict-right Xi zero: overlap order is `m`, Fisher numerator order is `m-1`, and quotient residue
  is exactly `2m`. C27 proved that centered scaling of this conormal is exactly the exceptional Xi
  affine-current residue `-(rho-1/2)m`, whose horizontal component is strictly negative off line.
  Producer moved upstream to a pre-divisor sign/annihilation theorem for this oriented residue.
- 2026-08-10 — C28 proved Route N reciprocal transport and Route T mass propagation use the same
  timelike boost coordinates. Route T phase has one exact saddle for `0<=h<u` and none for
  `0<u<=h`; `A` embeds as `u=(A+A^-1)/2`, `h=(A-A^-1)/2`, unit proper time. Route N holonomy,
  nonmetricity, C27 affine residue, and Route T saddle become orientation, energy, rapidity, and
  stationary coordinates of one conserved charge. New module compiles and is umbrella-wired.
- 2026-08-10 — C29 proved the C28 boost handoff determines Route T's exact spacelike curved-contour
  rate. Principal-root damping is the attained maximum over actual nonnegative contour angles,
  strictly beats horizontal null-gap decay, and yields sharp limiting slope
  `a/sqrt(a^2-1/4)<a/(a-1/2)`.
- 2026-08-10 — C30 proved exact branch-free full-line hyperbolic representation of mass Fourier
  transform. C31 proved one-sided entire contour deformation, exact Lorentz translation to
  order-one Schlaefli carrier, and coefficient-faithful `K_1` comparison. C32 proved maximizing
  contour is an actual interior angle and inserted exact principal-root rate. Full-exponent
  Fourier/Bessel lift is closed; residual open core is arithmetic timelike-plus-glancing
  cancellation.
- 2026-08-10 — C33 proved optimizer boost factor is uniformly bounded on every strict slope cone,
  converted `alpha>alpha_sharp(a)` into Dirichlet exponent `p>1`, and proved absolute summability
  of the complete centered sharp-spacelike atom family. Exact finite partition leaves only
  `log n<alpha*u`; prior spacelike-summation overreach is closed in Lean.
- 2026-08-10 — C34 proved every `alpha>1` admits a legal mass parameter whose complete
  sharp-spacelike complement is uniformly bounded, and proved RH exactly equivalent to residual
  boundedness on `log n<alpha*u`. Open arithmetic support is now arbitrarily close to causal cone.
