# Prime-circle recurrence character descent and tracial selection law

- **ID:** ULF-PMFM-2
- **Stage:** 3-formalized (paper proof companion)
- **Type:** THEOREM (paper)
- **Source:** ULF-PMFM-1; prime-log weld density; circle faithfulness; compact recurrence formation
- **Statement:** The prime-log formation lattice embeds faithfully and densely in the compact
  archimedean circle, but a real modular log character extends continuously through this compact
  recurrence completion exactly when it is zero.  For the theta-source recovered conormal current,
  such descent exists exactly on the critical line, and global descent is equivalent to RH.

## Goal

Supply the global formation/descent law isolated by ULF-PMFM-1 without replacing it by another
bounded-orbit scalar.  The construction must keep all finite prime histories distinct, close their
observer recurrence in a compact carrier, and ask whether the modular information recovered from
the theta conormal current survives continuously at the completion boundary.

The resulting theorem is a selection architecture, not an RH proof: existence, faithfulness, and
density of the compact prime formation are unconditional, while continuity of the theta modular
character at its new boundary is the exact remaining source theorem.

## Gates

- [x] 0 → 1 in-progress: canonical compact formation and exact recovery law identified
- [x] 1 → 2 fully-proven: complete proof below; every dependency is already proved in the corpus
- [x] 2 → 3 formalized: Lean modules and named leaf audit complete
- [ ] 3 → 4 publication-ready: standalone exposition and external audit pending

## 1. Universal compact-recurrence law

Let `L` be an abelian formation group.  A faithful compact recurrence formation consists of a
compact topological abelian group `K` and an injective homomorphism

`i : L -> K`

with dense image.  A real additive character `chi : L -> R` **descends through formation** if there
is a continuous additive character

`chi_bar : K -> R`

such that `chi_bar(i(l)) = chi(l)` for every `l in L`.  The equality is the common recovery law:
formation changes the carrier but erases none of the character value.

### Theorem 1 — compact real-character rigidity `[PROVED HERE]`

For every compact topological abelian group `K`, every continuous additive homomorphism

`phi : K -> R`

is zero.  Consequently, for every faithful compact recurrence formation `i : L -> K`,

`chi descends through i  <->  chi = 0`.

### Proof

The image `phi(K)` is compact in `R`, hence norm-bounded by some `C`.  If `phi(x) != 0`, choose a
natural number `n` with

`C < n |phi(x)|`.

Additivity gives `phi(n x) = n phi(x)`, contradicting the bound on `phi(K)`.  Thus `phi=0`.
If `chi` descends, exact recovery gives `chi(l)=phi(i(l))=0`.  Conversely the zero character
descends through the zero continuous character.  QED.

Faithfulness and density do not create the vanishing; they prevent it from being explained by
finite-history erasure.  Compactness of the completed observer history is the load-bearing law.

## 2. Canonical prime-circle formation

Let

`L_P = direct_sum_(p prime) Z`

be finite integer prime histories and define their real log lift

`lambda(c) = sum_p c_p log p`.

The archimedean unit period gives the circle `T=R/Z`.  Define

`i_P(c) = [lambda(c)] mod Z`.

### Theorem 2 — faithful dense compact prime recurrence `[PROVED HERE]`

The map `i_P : L_P -> T` is injective and has dense image.

### Proof

If `i_P(c)=0`, then `lambda(c)=k` for some integer `k`.  Exponentiating gives

`exp(k) = product_p p^(c_p) in Q`.

For `k != 0`, the left side is irrational by the formalized Hermite theorem for `exp(k)`, a
contradiction.  Hence `k=0`; unique factorization, equivalently integer linear independence of the
prime logarithms, gives `c=0`.  Thus `i_P` is injective.

The range contains every integer multiple of `[log 2]`.  Since `log 2` is irrational, this cyclic
subgroup is dense in `R/Z`.  Therefore the larger range of `i_P` is dense.  QED.

This is the object needed by the selection law: all finite prime formation histories remain
distinct, yet their observer closure is compact and recurrent.

## 3. Prime modular descent

For `t in R`, define the modular log character

`chi_t(c) = t lambda(c)`.

Its positive exponential is the group-completed reciprocal formation character from ULF-PMFM-1.

### Theorem 3 — exact prime modular descent classification `[PROVED HERE]`

There exists a continuous additive `chi_bar_t : T -> R` satisfying

`chi_bar_t(i_P(c)) = chi_t(c)` for every finite prime history `c`

if and only if `t=0`.

### Proof

The forward direction is Theorem 1 applied to the compact circle: `chi_bar_t=0`, hence
`t log 2=0`, and `log 2 != 0` gives `t=0`.  If `t=0`, take `chi_bar_t=0`.  QED.

This is stronger than orbit boundedness.  No fitted gauge, norm, probability, or divisor-dependent
compactification is used.  The prime histories are embedded injectively; the obstruction occurs
only when exact modular recovery is required to remain continuous after recurrent completion.

## 4. Theta-source current fusion

For a multiplicity-labelled Xi divisor copy `rho`, put

`t_rho = 2 Re(rho)-1`.

ULF-PMFM-1 constructs the theta reflection-pair root block, its nonzero recovered conormal current,
and the prime modular action.  For a finite prime history `c`, its modular log is exactly

`t_rho lambda(c)`.

This is not a new scalar inserted after divisor selection: each generator `log p` is the logarithm
of the literal reciprocal theta prime-translation energy, and the action commutes with exact current
recovery.

Define `ThetaXiPrimeModularCompactRecurrenceDescent(rho)` to mean that this recovered modular log
character descends continuously through the canonical faithful dense prime-circle formation.

### Theorem 4 — source-current tracial descent `[PROVED HERE]`

For every Xi divisor copy `rho`,

`ThetaXiPrimeModularCompactRecurrenceDescent(rho)`

holds if and only if

`Re(rho)=1/2`.

Functional-equation reflection changes `t_rho` to `-t_rho`; therefore descent is preserved by
reflection.  Globally,

`forall rho, ThetaXiPrimeModularCompactRecurrenceDescent(rho)`

is equivalent to the Riemann hypothesis.

### Proof

Theorem 3 gives descent iff `t_rho=0`.  The already proved centered-rate identity gives
`t_rho=0` iff `Re(rho)=1/2`.  Reflection negates the centered rate and therefore preserves its zero
locus.  Requiring the condition for every multiplicity-labelled Xi divisor copy places every
nontrivial zeta zero on the critical line; conversely RH supplies the line equation for every copy,
so every modular log character is zero and descends.  QED.

## 5. Mechanism and route-independent prediction

The law fuses five organs without identifying their scalar endpoints:

1. prime-log difference formation and unique factorization;
2. Hermite transcendence, which makes compact circle observation faithful;
3. compact recurrence, which closes the observer history;
4. theta functional-equation reflection and exact conormal-current recovery;
5. reciprocal prime modular dilation, whose open lifted history is the recovered real character.

It predicts a general fourth-organ theorem: whenever a route's noncompact real formation charge is
exactly reconstructible from a faithful compact recurrent observer completion, the charge must
vanish.  Every no-go that preserves a nonzero reciprocal charge is therefore a failure of continuous
descent at the completion boundary, not a failure of local positivity or reflection covariance.

This distinguishes the mechanism from regression.  Earlier routes asked for boundedness of a
zero-labelled character or built a receiver whose hypothesis already encoded the wall.  Here the
compact carrier, injective history formation, and dense recurrence are unconditional and
divisor-independent.  The only zero-dependent datum is the already source-produced modular
character whose boundary regularity is being tested.

## 6. Exact remaining producer

The global descent statement is RH-equivalent, so it must not be assumed.  The remaining producer
is now one concrete pre-zero theorem:

> Prove that the literal theta-source conormal recovery field, evaluated on finite prime histories,
> is uniformly continuous for the prime-circle recurrence topology and therefore extends across
> the compact completion boundary.

Equivalently, construct the extension from the theta source before choosing a divisor.  The present
theorem proves that any such extension is automatically information-neutral, unique on the dense
prime history, and tracial.  Missing Lean infrastructure for the extension is a construction task,
not a reason to change architecture.

## Door passport

- **Source purity:** finite prime histories, prime logarithms, archimedean unit period, literal theta
  prime translations, functional equation, and conormal current.
- **Faithfulness:** `i_P` is injective; no finite history is erased.
- **Recurrence:** `i_P(L_P)` is dense in the compact circle.
- **Recovery:** descended character must equal the original modular log on every finite history.
- **Multiplicity:** retained in complete theta root blocks and their conormal current.
- **Reflection:** internal; it negates modular log and preserves the descent locus.
- **Non-circularity:** compact formation existence, injectivity, density, and compact-character
  rigidity are unconditional.  Boundary continuity is explicitly marked as the remaining producer.
- **Selection consequence:** pointwise descent iff critical-line placement; global descent iff RH.

## Log

- 2026-08-31 — complete paper proof; promoted to Stage 2 after corpus overlap audit
- 2026-08-31 — formalized compact rigidity, faithful dense prime recurrence, exact source descent,
  functional-equation invariance, and global RH interface; promoted to Stage 3
