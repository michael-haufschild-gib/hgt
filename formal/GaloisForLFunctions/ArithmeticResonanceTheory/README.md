# Arithmetic Resonance Theory (ART)

Namespace `GaloisForLFunctions.ArithmeticResonanceTheory`; umbrella `ArithmeticResonanceTheory.lean`.

**Question.** The zeros of $\zeta$ are *resonances*: poles of a meromorphic continuation, of
$\zeta'/\zeta$, of a scattering matrix, of a dynamical zeta function. Every positive object the corpus
owns — Haar measure, Laplacians, Dirichlet forms, Gram matrices, KMS states — has a *spectrum*, and a
resonance is a spectral point only of an operator built from the zeros. Outside positivity mathematics
knows two mechanisms that control resonances: **amplification**, which sharpens a bound that is
uniform over a family into the sharp bound at one member, and **oscillation**, which produces
resonance-free strips from cancellation in twisted transfer operators. Which realizations of the
primes can carry these mechanisms, what does each yield, and what exactly is missing over $\mathbb Z$?

ART is the theory of **realizations, resonances and amplifiers** for Euler products. Its basic object
is a *realization*: a symbolic or graph dynamical system whose dynamical zeta function is $\zeta$.
Its basic distinctions are between a *spectral pole* (an eigenvalue of a transfer operator crossing
$1$) and a *nuclearity pole*, between the *even* part of a realization (poles) and its *odd* part
(zeros), and between *fixed* and *envelope* losses of an amplifier. Every statement is unconditional;
RH and zero-free strips appear only as conclusions of implications or inside equivalences.

---

## 1. Place in the research

The three walls Σ, Π, Γ are one fact read three ways: the explicit formula is the argument principle
with a holomorphic weight, it computes reflection pairings and never same-point sums, and every
positive object sees spectra. Most of what a theory of resonances needs is owned by existing
programmes; two items are not: a **non-envelope amplifier**, and an **oscillation mechanism on a
realization of the primes** that escapes the Ruelle no-go. ART owns these two items and the
realization theory they require.

| Programme | Interface |
|---|---|
| ArithmeticCriticalityTheory (ACT) | Ground states and supersolutions: the positive (spectral) side ART contrasts with |
| ScaleSignedIncidenceCriticality, SquareRootThreshold, ArithmeticOrientationGeometry | Depth as a rate; rate = depth of the deepest seen zero. ART's rate–depth law for finite exponential sums is the amplifier's engine; AOG's self-upgrade is its iteration step over $\mathbb Z$ |
| ConjugateDiagonalGeometry (CDG), HilbertianExplicitFormulas (HEF) | Same-point sums, collision quantum, explicit-image rigidity: why the explicit formula cannot see resonances as spectra |
| ArithmeticCastelnuovoSeveri (ACS) | Finite-field calibration, golden datum, infinite genus; ART's rank law is the counting form of infinite genus |
| ArithmeticPositiveDuality | Bost–Connes temperature = Hecke exponent; the BC partition function is the commutative realization's zeta |
| DilutionCrystallizationPincer | Kronecker and Baker on the prime torus; the same independence defeats oscillation on additive realizations |
| TransThresholdPairCorrelation (TTPC) | Tensor powers of a scale trace are prime correlations; an identity amplifier at level 2 is a signed Hardy–Littlewood moment |
| HeckeKreinToeplitz, ArithmeticKreinLangerTheory | Krein index of the Weil kernel: the resonance count as a negative-square count |
| `RHTower` dynamical zetas | `RuelleZetaNuclearZeroFree`: nuclear analytic expanding Markov zetas are zero-free on $\Re s>\sigma_0-1$; $\zeta$ is not one of entropy $\le1$ |
| `HTGeometry` symbolic dynamics | `SymbolicRuellePollicott`: Hölder suspensions of mixing subshifts are reciprocals of holomorphic functions on $\Re s>1-\varepsilon$; ART reuses its shift spaces, Birkhoff sums and Hölder potentials |
| `HTGeometry` determinants | `FiniteDeterminantLogSeries`: $\det(1-A)=\exp(-\sum_k\operatorname{tr}A^k/k)$, the even-realization formula |
| `RHTower` envelopes and Landau | `DensityEnvelopeNoGo`, `ZetaMultipleLandauZeroFree`, Chen–Gupta–Li modules: the existing amplifier attempts |

---

## 2. Why

**Resonances, not spectra.** A self-adjoint operator has real spectrum and a positive form has a
sign; the zeros of $\zeta$ are neither. They are poles of the continuation of $-\zeta'/\zeta$, which is
not the resolvent of any operator built without the zeros. The explicit formula is holomorphic and
rigid: a holomorphic weight agreeing with $|F|^2$ on the critical line equals $F\cdot F^\#$, so no test
function makes it compute a same-point (spectral) sum. Positivity meets the zeros only at the
endpoint, where the sign is RH itself.

**Two mechanisms that do not need positivity.** (i) *Amplification.* Deligne bounds one Frobenius
eigenvalue by a moment over a family of tensor powers: each member contributes non-negatively, the
total is bounded with a loss that does not grow with the tensor power, and roots remove the loss.
(ii) *Oscillation.* Dolgopyat contracts twisted transfer operators $\mathcal L_{\sigma+it}$ uniformly in
$|t|$, which pushes resonances off a strip. Both act on resonances directly.

**Realizations.** Oscillation needs a transfer operator, hence a *realization*. Two exist for free.
The *commutative* one (one loop of length $\log p$ per prime) has zeta $\zeta$, but its transfer
operator is diagonal, not mixing, and its pole at $1$ is a breakdown of nuclearity. The *free* one
(one vertex, a loop per prime) is mixing, with zeta $1/(1-P(s))$ and entropy $\sigma^\ast\in(1,2)$: it
overcounts. Every realization lies between commutativity (right zeta, no dynamics) and freeness
(dynamics, wrong zeta). Unique factorization forbids concatenating orbits additively; integrality
forbids concatenating them too smoothly; the archimedean place forbids a finite odd part.

**The payoff and its price.** A realization by a Hölder suspension of a mixing finite-type subshift
makes $\zeta$ the reciprocal of a holomorphic function on $\Re s>1-\varepsilon$: a zero-free strip,
which no method gives. A nuclear analytic realization would give too much and is excluded. ART
proves that the strip costs regularity: the Hölder modulus $\theta$ of such a roof satisfies
$\theta\,e^{\varphi(a^\infty)}\ge1$ at every re-enterable fixed point.

**Amplifiers.** Over $\mathbb F_q$ the family loss in Deligne's argument is fixed in the tensor power,
and the degree-$k$ monomials in $2g$ Frobenius eigenvalues number $\binom{2g+k-1}{k}$, polynomial in
$k$. Over $\mathbb Z$ the rank is infinite: an orthogonal family separating the degree-$k$ monomials in
$r$ prime phases has at least $\binom{r+k-1}{k}$ members, and this size exactly pays for the gain.
Orthogonality is an envelope; a non-envelope amplifier over $\mathbb Z$ must evaluate its moments by an
identity.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Dynamical zeta | $\exp\sum_{n\ge1}n^{-1}Z_n(s)$, $Z_n(s)=\sum_{\sigma^nx=x}e^{-s\varphi^n(x)}$ | `periodicZ`, `periodicSumR` (HTGeometry) |
| Realization of $\zeta$ | a roof $\varphi\ge r_{\min}>0$ on a subshift with dynamical zeta $=\zeta$ on $\Re s>1$ | hypothesis `hreal` of `isPrimeLength_of_realization` |
| Prime-length system | every periodic point of least period $L$ has $e^{\varphi^L(x)}$ prime | `IsPrimeLength`, `IsAdditivePrimeLength` |
| Commutative realization | disjoint loops of length $\log p$; diagonal transfer operator with eigenvalues $p^{-s}$ | `commEigen`, `commTrace` |
| Free realization | one vertex, a loop of length $\log p$ per prime; $n$-th trace $P(\sigma)^n$ | `freeTrace`, `primeZetaR` |
| Additive realization | locally constant roof (an edge-weighted graph), any alphabet | `IsAdditivePrimeLength`, `IsFirstReturn` |
| Finite even realization | finite weighted graph, $Z=1/\det(1-M(s))$ | `graphMatrix`, `graphZeta` |
| Finite virtual realization | $Z=\det(1-M^-(s))/\det(1-M^+(s))$ | `riemannZeta_ne_virtualRealization` |
| Exponential polynomial | $\sum_jc_je^{-\lambda_js}$, $\lambda_j\in\mathbb R$ | `IsExpPoly` |
| Cycle family | periodic points $(u^nv)^\infty$ shadowing $u^\infty$ | `IsCycleFamily`, `familyPoint`, `fixedPointFamily` |
| Return word | starts at a symbol, avoids it, returns to it | `IsReturnWord` (subshifts), `IsFirstReturn` (any alphabet) |
| Conformal defect | $m_n=p_{n+1}-a\,p_n$, $p_n=e^{\varphi(u^nv)}$, $a=e^{\varphi(u)}$; an integer | `IsDefectChain` |
| Relative Dolgopyat bound | $\lvert Z_n(\sigma+it)\rvert\le C\rho^nZ_n(\sigma)$ for $t\ge T$, $\rho<1$ | `RelativeDolgopyat` |
| Phase | $e^{-it\ell}$ of an orbit of length $\ell$ | `phase` |
| Amplifier moment | $\lvert a(n)\rvert^{2k}\le C(B^{2k}D)^n$, $a(n)=\sum c_i\alpha_i^n$ | `norm_le_of_moment_bound` |
| Brauer family | degree-$k$ monomials of unimodular phases orthogonal over the family | `IsBrauer`, `monomial` |
| Mass at a length | $\sum_{\lambda_i=t}w_i$ of a generalized Dirichlet series | `massAt` |
| Signed length series | periodic points $(+1/n)$ against prime powers $(-1/(k+1))$ | `signedWeight`, `signedLength`, `OrbitIndex` |

**Words.** *Spectral pole*: a pole where an eigenvalue of $\mathcal L_s$ crosses $1$. *Nuclearity pole*: a
pole created by divergence of the trace norm while the spectral radius stays below $1$. *Even / odd
part*: the denominator / numerator determinant of a virtual realization; poles come from the even
part, zeros from the odd part. *Conformal threshold*: junction distortion $a^{-n}$ along a cycle
family; *super-conformal* below it. *Fixed loss*: the moment loss $D$ does not depend on the tensor
power; *envelope loss*: $D_k=e^{2k\lambda}$, loss exponent $\lambda$. *Rank*: number of independent
phases a family must separate — $2g$ over $\mathbb F_q$, $\pi(x)$ over $\mathbb Z$ at scale $x$.
*Pole-killing*: removing the frequency above the target bound from a family moment.

---

## 4. Mechanisms

1. **Euler product = commutative realization.** $\exp\sum_n n^{-1}\operatorname{tr}\mathcal L_s^n=\zeta(s)$
   (`exp_tsum_commTrace_eq_riemannZeta`); eigenvalues have modulus $\le2^{-\sigma}$ and none equals $1$
   (`norm_commEigen_le`, `commEigen_ne_one`); trace class iff $\sigma>1$ (`summable_norm_commEigen_iff`);
   the trace norm $P(\sigma)\to\infty$ as $\sigma\downarrow1$ (`tendsto_primeZetaR_nhdsGT_one`).
2. **Renewal = free realization.** Words give $Z_n=P^n$ (`hasSum_prod_words`, `freeTrace_eq_pow`),
   zeta $(1-P)^{-1}$ (`exp_tsum_freeTrace_eq`); $P$ strictly decreasing (`primeZetaR_strictAntiOn`),
   $P(2)\le\pi^2/6-1<1$ (`primeZetaR_two_lt_one`).
3. **Unique factorization forbids additive concatenation.** Two first-return words at a symbol
   concatenate to a primitive orbit (`minimalPeriod_concat`) of length $\log(pq)$.
4. **Even realizations are pole-only.** $\det(1-A)=\exp(-\sum_k\operatorname{tr}A^k/k)$ for small entries
   (`det_one_sub_eq_exp`, via `norm_trace_pow_succ_le`), so $Z\cdot\det(1-M)=1$ and $\det(1-M)$ is entire.
5. **Exponential polynomials cannot vanish on a real progression** unless identically: along
   $s_0+hk$ they are finite exponential sums in $k$ with distinct positive bases
   (`eq_zero_of_vanish_on_progression`). The trivial zeros of $\zeta$ lie on such a progression.
6. **Uniqueness of generalized Dirichlet series** with locally finite frequencies: least bad
   frequency, gap, tail $O(e^{-\sigma(t_0+\delta)})$ (`massAt_eq_zero_of_tsum_eq_zero`). Reads the length
   spectrum of a realization off $\zeta$: a periodic point of least period $L$ carries mass $\ge1$ at
   its length; a prime power $p^{k+1}$ carries $1/(k+1)$.
7. **Integrality forbids super-conformal distortion (Pisot).** If $p_{n+1}=a\,p_ne^{\delta_n}$ with
   $|\delta_n|\le K\rho^n$, $a\rho<1$, the integers $p_{n+1}-ap_n$ tend to $0$ and vanish
   (`eventually_succ_eq_mul_of_ratio`): composite (`not_eventually_prime_of_ratio`).
8. **Affine recurrences meet a member (Cunningham).** Modulo $\ell=p_M$, $x\mapsto ax+m$ is a
   permutation whose orbit returns to $0$ (`exists_dvd_of_injective_step`,
   `not_eventually_affine_recurrence`); the same along residue classes for periodic defects
   (`not_eventually_periodic_defect`). Hence no conformal expansion
   (`not_eventually_prime_of_conformal_expansion`).
9. **Bounded distortion along cycle families.** For a $(C,\theta)$-Hölder roof,
   $|\varphi(x_{n+1})-\varphi(u)-\varphi(x_n)|\le2C\theta^{nL}/(1-\theta)$ (`abs_familyStep_le`).
10. **Pollicott continuation.** Reciprocal of a holomorphic function on $\Re s>1-\varepsilon$; the residue
    factor and the identity theorem transfer it to $\zeta$ (`riemannZeta_ne_zero_of_holderRealization`).
11. **Simultaneous approximation.** Finitely many phases return to $1$ at arbitrarily large $t$
    (`exists_ge_forall_norm_phase_sub_one_lt`); absolutely convergent exponential sums return to their
    untwisted value (`exists_ge_norm_tsum_twist_lt`); word phases multiply (`phase_sum`,
    `norm_sum_words_twist_le`).
12. **Rate = depth.** An almost periodic sum tending to $0$ has zero coefficients
    (`coeff_eq_zero_of_tendsto`, difference operator); $|a(n)|\le KR^n$ bounds every present frequency
    by $R$ (`norm_le_of_eventually_norm_le`).
13. **Moments lose a root; positivity transfers family moments** (`norm_le_of_moment_bound`,
    `norm_le_of_family_moment_bound`).
14. **Congruence forcing of bounded defects.** Bounded conformal defects are nonzero, prime to $a$,
    and of fixed parity (`IsDefectChain.defect_ne_zero`, `not_dvd_defect`, `two_dvd_defect`). If a fixed
    modulus determines the defect, the residues follow a self-map of $\mathbb Z/L$ and the defects become
    periodic (`IsDefectChain.false_of_determined`): two values in different nonzero classes mod $3$
    (`false_of_two_classes_mod_three`), or a unipotent walk $x\mapsto x+r$ mod $\ell$ that can take only
    finitely many $r$-steps (`false_of_unipotent`).
15. **Orthogonality pays for itself.** Orthogonal nonzero monomial vectors in $\mathbb C^X$
    (`card_sym_le_card_of_isBrauer`); multinomial expansion, diagonal moment, Cauchy–Schwarz
    (`pow_sum_le_moment_of_isBrauer`).

---

## 5. Pillar theorems

1. **The two realizations.** The commutative realization realizes $\zeta$ and its pole is a nuclearity
   pole (`exp_tsum_commTrace_eq_riemannZeta`, `commutative_pole_is_nuclear`); the free realization has a
   spectral pole at a unique entropy $\sigma^\ast\in(1,2)$ (`free_pole_is_spectral`).
2. **Additive rigidity.** In an additive prime-length shift on any alphabet each symbol has at most one
   first-return word (`firstReturn_unique`): additive realizations are commutative. The free realization
   is not prime-length (`not_isAdditivePrimeLength_full`).
3. **Parity.** A finite weighted graph has $Z\cdot\det(1-M)=1$ (`graphZeta_mul_det_eq_one`): even
   realizations are zero-free, and $\zeta$ is none (`riemannZeta_ne_graphZeta`).
4. **The archimedean place forbids finite odd parts.** $\zeta$ is no finite virtual realization
   (`riemannZeta_ne_virtualRealization`): the trivial zeros would make the odd determinant vanish.
   Calibration: over $\mathbb F_q$ the zeros of the odd determinant are exactly the spectrum of the
   finite odd operator (`det_one_sub_cpow_smul_eq_zero_iff`), they repeat along vertical progressions
   (`cpow_add_period`), and RH is unitarity (`re_eq_half_of_norm_eigenvalue`).
5. **A realization of $\zeta$ is prime-length** (`isPrimeLength_of_realization`), by uniqueness of
   generalized Dirichlet series (`massAt_eq_zero_of_tsum_eq_zero`).
6. **The conformal threshold.** Prime cycle families are never super-conformal and never obey a
   conformal expansion or a periodic conformal defect (`not_eventually_prime_of_ratio`,
   `not_eventually_prime_of_conformal_expansion`, `not_eventually_periodic_defect`). For Hölder roofs:
   $a\,\theta^L\ge1$ along every prime cycle family (`one_le_mul_pow_of_cycleFamily`). Two different
   return words $u,v$ at a symbol give a primitive family $(u^nv)^\infty$ (`minimalPeriod_familyPoint`),
   so in a prime-length system $\theta^{|u|}e^{\varphi^{|u|}(u^\infty)}\ge1$ along every re-enterable
   cycle (`one_le_exp_mul_pow_of_returnWords`; fixed points: `one_le_exp_mul_of_isPrimeLength`).
7. **The strip and its price.** A Hölder realization of $\zeta$ on a mixing subshift gives
   $\zeta\ne0$ on $\Re s>1-\varepsilon$ (`riemannZeta_ne_zero_of_holderRealization`) and has Hölder modulus
   $\theta\ge p_u^{-1/|u|}$ along every re-enterable cycle $u$ of prime $p_u$
   (`one_le_exp_mul_pow_of_holderRealization`, `one_le_exp_mul_of_holderRealization`).
8. **Oscillation fails on additive and free realizations** (`not_relativeDolgopyat_of_finite_edges`,
   `not_relativeDolgopyat_free`); twisting the commutative realization changes no eigenvalue modulus
   (`norm_commEigen_twist`).
9. **The amplifier law.** Fixed loss gives the sharp bound (`norm_le_of_fixed_loss`) and forces
   pole-killing (`pole_coefficient_eq_zero`); an envelope loss $e^{2k\lambda}$ gives $Be^\lambda$, attained
   (`envelope_moment_bound_attained`).
10. **The Mills boundary, decided cases.** $p_n=Ca^n+O(1)$ iff the defects are bounded
    (`abs_defect_le`). No prime chain has defects $|m|\le2$ for even $a$ with $3\nmid a$
    (`not_isDefectChain_of_even`), $|m|\le3$ for odd $a$ with $3\nmid a$ (`not_isDefectChain_of_odd`),
    or $|m|\le1$ for odd $a$; for every real $C$, $\lfloor Ca^n\rfloor$ is not eventually prime for
    $a=2,\dots,6$ (`not_eventually_prime_floor`), and no primes stay within $\tfrac12$ of $Ca^n$ for
    $a\in\{2,4,5\}$ (`not_eventually_prime_near`). For a realization this means: along a cycle of prime
    $2$ the junction defect exceeds $2$, along a cycle of prime $\ge5$ it exceeds $3$, infinitely often.
11. **The rank law.** Brauer families have $\ge\binom{r+k-1}{k}$ members and their $2k$-th moment is at
    least the $2k$-th power of the trivial bound (`pow_sum_le_moment_of_isBrauer`); the per-power cost
    tends to $1$ at fixed rank (`tendsto_choose_rpow_inv_of_fixed_rank`) and is $\ge r/k$ at rank $r$
    (`rank_div_le_choose_rpow_inv`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| $\zeta$ is the zeta of the prime dynamics | Of the commutative realization only, which has no dynamics |
| Mixing the prime orbits keeps $\zeta$ | Free mixing gives $(1-P)^{-1}$ with entropy $\sigma^\ast>1$ |
| The pole at $1$ is a Perron–Frobenius eigenvalue | In the commutative realization the spectral radius is $\le\tfrac12$; the pole is a nuclearity breakdown |
| Oscillation gives the strip | In a finite-type Hölder realization the strip comes from the continuation; the zeros of $\zeta$ are not transfer-operator resonances there. The difficulty is the realization |
| A smoother roof is a better realization | Integrality forbids super-conformal roofs: $\theta\ge e^{-\varphi(a^\infty)}$ |
| A finite odd part could carry the zeros | The trivial zeros lie on a real progression; no exponential polynomial vanishes there |
| Independent lengths help oscillation | Kronecker independence returns all phases at once; additive data never contract uniformly |
| A family moment with a small constant amplifies | Only the growth of the loss in $k$ matters; envelope losses are attained |
| Orthogonality is the amplifier's engine | Orthogonality pays for itself exactly; gains need an identity |
| Big monodromy is the missing structure | At the level of counting the missing structure is finite rank; $\mathbb Z$ has infinite genus |
| Realization obstructions are analytic | ART's obstructions use integrality and unique factorization; they fail for Beurling systems, as they must |
| "Realization" is a picture | It is the zeta identity; it implies prime-length by uniqueness of Dirichlet expansions |

---

## 7. Questions and answers

1. **Realization.** *Which dynamical systems realize $\zeta$, and what does each class yield?*
   No finite graph, even or virtual (pillars 3, 4). Additive realizations on any alphabet are
   commutative (pillar 2). Every realization by a positive roof on a subshift of finite type is
   prime-length (pillar 5), so its cycle families are never super-conformal and its Hölder modulus is
   bounded below at every re-enterable cycle (pillar 6). Such a realization would yield a zero-free
   strip (pillar 7). At the conformal threshold its junction defects are unbounded or bounded but
   unforced by congruences (pillar 10). What survives: Hölder roofs at or below the conformal threshold
   with such defects, and non-additive roofs on countable alphabets.
2. **Oscillation.** *Where does a twisted transfer operator contract, and is oscillation needed?*
   Never on additive or free realizations, and the commutative one has nothing to contract (pillar 8).
   In a finite-type Hölder realization the strip needs no oscillation at all (pillar 7). Oscillation
   can only enter through a non-additive roof, which is the realization problem itself.
3. **Amplification.** *What converts a family bound into the sharp individual bound, and what replaces
   big monodromy?* Positivity, a loss fixed in the tensor power, and rate = depth (pillar 9); an envelope
   loss yields exactly its strip. At the level of counting the role of big monodromy is played by
   finite rank: orthogonality costs $\binom{r+k-1}{k}$, subexponential in $k$ only at fixed rank, and never
   beats the trivial bound (pillar 11). Over $\mathbb Z$ every orthogonality amplifier is an envelope.
4. **Resonance–spectrum dictionary.** Spectral poles (free) versus nuclearity poles (commutative)
   (pillar 1); even parts give poles only (pillar 3); zeros need an odd part; over $\mathbb F_q$ the odd
   part is finite ($H^1$) and the zeros are its spectrum; over $\mathbb Z$ the archimedean place forbids a
   finite odd part (pillar 4).
5. **Graded versus critical.** Strips: a Hölder realization (pillar 7), an envelope loss (pillar 9).
   The line: a fixed loss (pillar 9). Sharp boundaries: the conformal threshold (pillar 6), the Mills
   boundary (pillar 10), the rank law (pillar 11).

## 8. Tools

A realization calculus over shift spaces and graphs (cycle families, first-return words, prime-length
systems); arithmetic obstructions (Pisot, Cunningham, unique factorization, trivial zeros); the
uniqueness of generalized Dirichlet series as a reader of length spectra; the realization–strip bridge;
oscillation diagnostics (phases, returns, relative Dolgopyat bounds); the amplifier calculus (rate =
depth, moment roots, fixed and envelope losses, pole-killing); the rank law for orthogonal families.

## 9. Open research topics

1. **The Mills boundary.** Is there a prime sequence $p_n=Ca^n+O(1)$? Decided impossible where a
   fixed modulus forces the bounded defect (pillar 10). Open where congruences only confine the
   residue walk without forcing periodicity: defects $\pm1$ with $6\mid a$, $\pm2$ with $a=3$,
   integer parts for $a\ge7$, nearest integers for $a=3$ and $a\ge6$. For $a=6$ and defects $\pm1$,
   moduli $5$ and $7$ bound the partial sums of the defects over even and over odd indices, which
   aperiodic sequences satisfy. A branching count — at most $2M+1$ continuations per step, each prime
   with probability $\asymp1/(n\log a)$ — predicts that no chain exists; a proof must use moduli that
   grow along the chain, as the Cunningham argument does with $\ell=p_N$.
2. **Sub-conformal realizations.** Construct or exclude Hölder realizations with
   $\theta e^{\varphi(a^\infty)}\ge1$ everywhere; relate the admissible $\theta$ to the strip width.
3. **Countable alphabets.** Non-additive realizations over the infinite prime alphabet (the
   Bost–Connes classical system): continuation, Gurevich pressure, and where oscillation is needed when
   the transfer operator is not quasi-compact.
4. **Infinite-rank odd parts.** Virtual realizations with infinite-dimensional odd part carrying the
   trivial zeros (a Gamma factor) and the nontrivial ones; relation to the Krein index and to Σ6.
5. **Identity amplifiers over $\mathbb Z$.** Family moments evaluated by an explicit formula on a single
   total space, with loss fixed in $k$; the signed Hardy–Littlewood moment of TTPC as the level-2 case.
6. **Amplifier audit of Chen–Gupta–Li.** Classify its loss: fixed, envelope, or rank-limited.

## 10. Success criteria and contributions

**Success.** A strip or the line from a mechanism of ART, or a classification that closes a mechanism
with a sharp boundary and a formalized positive survivor.

**A contribution** is unconditional and formalized; is stated in realizations, cycle families,
transfer operators, families and losses; says what it gives over $\mathbb F_q$ (curves: lattice lengths
$d\log q$, finite odd part $H^1$), on the golden datum, on Beurling systems and on the free realization;
uses integrality, unique factorization or the archimedean place where it claims selectivity for
$\mathbb Z$; separates graded conclusions (rates, strips) from critical ones (the line); and records the
positive survivor of every no-go.

**Battery.** Curves over $\mathbb F_q$ (calibration); the golden datum $1-5X+5X^2$ (fake curve);
Beurling systems with zeros near $\Re s=1$ (non-integral lengths); the free prime realization; finite
graphs.

**Principles.** Resonances are not spectra; a realization is a theorem, not a picture; integrality is
margin; only the growth of a loss matters; orthogonality is not amplification; calibrate over
$\mathbb F_q$.
