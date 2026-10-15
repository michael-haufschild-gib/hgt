# EWU: double-pole branch exclusion

Status: FORMALIZED. The double-pole branch is eliminated; the negative-part divergence branch remains open.

## Objective and constraints

Overcome a structural obstruction in even pole-weight uniqueness. No improved
estimate, RH equivalence, conditional receiver, numerical experiment, web search,
or literature novelty audit counts as success. Use current Lean source and corpus
search. Formalize only dependency-closed results; audit leaf modules with
`lake env lean`, targeted dependencies with `--old`, and formal lint. Do not build
umbrellas or modify unrelated work.

## Plan

1. Locate exact EWU frontier in Lean; search across corpus for structural tools.
2. Conjecture, attack, record failure or complete paper proof, then iterate.
3. Formalize a surviving significant result without unproved premises.
4. Audit proof, axioms, imports, lint, and significance before claiming success.

## Corpus facts checked

- `EvenSectorWeilCone`: even Farkas and monotonicity in pole weight.
- `EvenSectorFullPositivity`: pole weight one gives full positivity and pins weights.
- `EvenSectorPoleFreeResonatorPositivity`: pole-free cosine-shift measures and
  positivity for resonators with nonnegative translation coefficients.
- `EvenSectorTwistedArcNull`: full twisted-arc null family kills imaginary spectrum
  at pole weight one; its zeroth member has nonzero pole contribution.
- `EvenSectorPoleFreeLogThreshold`: sublogarithmic lower floors pin weights; this
  leaves arbitrary-sign weights and is not the target of this task.

## Conjectures under attack

### C1: pole annihilation preserves joint prime blindness

Try applying a pole-annihilating differential multiplier to the known Xi-divisible
joint null family, then use its nonnegative spectral lift to remove imaginary
mass for arbitrary pole weight. [OPEN CORE]: joint blindness need not survive
differentiation of correlations; values at log n do not determine their jets.
No theorem or formalization claimed.

### C2: recover a half-polar null family without its zeroth member

Inspect exact shifted-Gamma recurrence and twisted-arc moment constraints. The
first Gamma factor vanishes at one pole, but sign changes across that pole on the
imaginary axis. [OPEN CORE]: simultaneous prime blindness, spectral sign, and
nontriviality. No theorem or formalization claimed.

### C3: use forward modular dilation to preserve blindness and remove poles

The corpus already constructs arbitrary-order strip-edge vanishing with
self-reciprocity and positive critical Mellin transform. Its blind sublattice
shrinks under the symmetric filter. Forward dilation restores all integer
nodes, but introduces a Mellin phase. Recentering removes that phase and loses
the restored nodes. This construction does not supply the required simultaneous
positivity and blindness. It is not a counterexample to their joint existence.

### C4: exclude pole derivatives using finite pole slack

A positive form supported on a pole's value and first derivative cannot contain
a nonzero mixed derivative term without a derivative-square term. This algebraic
observation alone is routine and does not connect arbitrary arithmetic weights
to such a representation. Do not count it as an EWU contribution.

### C5: raise the twisted modular differential filter

The existing twisted generator is the square of the dilation operator; its
minimum principle produces the known null family. Two additional applications
would supply a squared pole-annihilating factor. The needed higher-order minimum
principle has not been proved. The existing second-order stream minimum principle
does not automatically imply it. [OPEN CORE].

### C6: double-pole branch exclusion — proof completed

The exact even-translate Gram identity excludes a polynomial factor at the
boundary of the arithmetic kernel's exponential type. The Abel transform then
excludes every negative double-pole obstruction, including oscillatory behaviour
for which a double-pole limit does not exist. This eliminates an entire branch
of the previous EWU alternative.

The result is a classification of the whole even-positive cone, with no extra
convergence or Abel premise:

For every real pole weight beta and every arithmetic source lambda positive on
all even tests, either

1. `lambda(n) = vonMangoldt(n)` for every `n >= 2`, or
2. for some real `sigma > 1`, the nonnegative series
   `sum_n max(-lambda(n),0) / n^sigma` is not summable.

“Super-pole” in the theorem name means this divergence alternative. It does not
assert meromorphic continuation or the existence of an actual pole. The
super-pole branch remains open; this is not full EWU closure or a proof of RH.

## Dependency-closed paper proof

Use the corpus's fixed real even smooth compact bump `g = farBump`. Its
correlation kernel `k = farKernel` has support strictly inside `(-log 2,log 2)`.
Write `J = integral g(x) exp(-x/2) dx > 0`,
`e_t(x) = g(x-t)+g(x+t)`, and
`S(a) = sum_{n>=2} lambda(n)/sqrt(n) k(log n-2a)`.
Let `Q` be the actual real pole-weighted Weil quadratic form.

Define

`A(t) = (1/(2 pi)) integral |FT(g)(r)|^2 cos(tr) gammaBracket(r) dr`,

`C(t) = beta J^2 (exp(-t/2)+exp(t/2)) + A(t) - S(t/2)`,

and `q=C(0)`. All identities below concern these actual source functions.

### 1. Exact Gram law

Support separation gives `atomPairing(g,g)=0`,
`atomPairing(g,e_t)=2 S(t/2)`, and `atomPairing(e_t,e_t)=2 S(t)` for `t>=0`.
Fourier translation gives `FT(e_t)=2 cos(tr) FT(g)`; hence the cosine double-angle
identity gives the exact archimedean quadratic expansion. The pole integral is
`J(1+c(exp(-t/2)+exp(t/2)))`. Combining these identities yields

`Q(g+c e_t) = q + 4c C(t) + 2c^2(q+C(2t))`.

Even positivity gives `q>=0` and nonnegativity of this polynomial for every real
`c`. Its discriminant therefore gives

`2 C(t)^2 <= q(q+C(2t))`.

The prime coefficient in `C` is one: its normalized translate is `e_t/2`.

### 2. Doubling removes the polynomial factor

Suppose `C(t)<=M exp(bt)` for all `t>=0`, with `b>=0`. The Gram law implies
`C(t)<=2q exp(bt)`, independently of `M`. If `q=0`, the Gram law forces `C=0`.
Otherwise, a violation at `t` gives `r=C(t)/(2q)>exp(bt)>=1`. Inductively,

`C(2^n t) >= 2q r^(2^n)`.

For the induction, the Gram law and the preceding lower bound imply that
`C(2^n t)>=2q`, and its next value exceeds the square divided by `2q`.
The exponential upper bound would bound `(r/exp(bt))^(2^n)` uniformly. This
contradicts divergence of powers of a real number greater than one.

### 3. Connect the exponential type to the arithmetic source

For this step assume the absolute Dirichlet series converges at every exponent
`>1`; the final classification removes this assumption by a case split.
For every `s>0`, the corpus's exact coefficient identity is

`(lambda(n)/sqrt(n)) exp(-(1/2+s) log n) = lambda(n)/n^(1+s)`

on `n>=2`. Compact support and boundedness of `k` therefore bound
`|S(t/2)|` by `D_s exp((1/2+s)t)`. The archimedean integral is uniformly bounded,
and the pole part has type `1/2`. Thus `C` has every type `1/2+s`.
Apply the doubling result with `s/2` at `2a`. There is one constant `K>=0`,
independent of `s`, such that

`S(a) >= -K exp((1+s)a)` for all `s>0`, `a>=0`.

### 4. Exact Abel transform and pinning

The existing source identity, with absolute integrability proved in the corpus,
is

`integral S(a) exp(-(1+2s)a) da = farLaplace(s)/2 * oddDirichlet(lambda,s)`.

`S(a)=0` for `a<=0`. Integrating the preceding floor over the positive ray gives

`farLaplace(s)/2 * oddDirichlet(lambda,s) >= -K/s`.

For `0<s<=1`, the corpus gives
`farLaplace(s)/2 >= exp(-1/6) J^2/2 = c0 > 0`.
If `s*oddDirichlet(lambda,s)` is negative, multiplying it by this inequality
and by the preceding Abel inequality gives

`s*oddDirichlet(lambda,s) >= -K/c0`.

The same conclusion is immediate when that quantity is nonnegative.
Consequently, for every `epsilon>0`, eventually as `s` approaches zero from
above,

`-epsilon <= s^2*oddDirichlet(lambda,s)`.

The existing Abel pinning theorem now applies without an additional double-pole
hypothesis and identifies every weight on `n>=2` with von Mangoldt.

### 5. Classification of the entire cone

The corpus already proves convergence of the positive part at every exponent
`>1` for every even-positive source. If the negative part also converges at all
these exponents, their sum gives the absolute convergence used in steps 3–4,
and the source is canonical. Otherwise a real exponent `>1` witnesses divergence
of the negative part. This proves the stated unconditional cone classification.

## Positive survivor and significance

The obstruction is a precise rigidity law: all even-positive sources of absolute
Dirichlet abscissa at most one are canonical. The proof produces and checks the
exact arithmetic cosine Gram kernel that forces this rigidity. The result
removes the old independent negative-double-pole possibility from EWU; it adds
no new premise to EWU and does not assert that the surviving divergence branch
is empty.

C1–C5 were attempted mechanisms, not proved universal impossibility statements.
Their unresolved simultaneous-blindness and positivity requirements remain open.

## Formalization and audit

Implementation: `formal/GaloisForLFunctions/RHTower/EvenSectorDoublePoleExclusion.lean`.
Main declaration: `RHTower.EvenSector.canonical_or_negative_superpole`.
The source is wired into `RHTower.lean`.

Audits completed:

- `lake --old build GaloisForLFunctions.RHTower.EvenSectorDoublePoleExclusion`:
  passed. Only the requested leaf and its dependencies were targeted; no umbrella
  or full-project build was run. Dependencies replayed existing warnings; the new
  module emitted none.
- `lake env lean GaloisForLFunctions/RHTower/EvenSectorDoublePoleExclusion.lean`:
  exit 0, no output.
- `lake env lean /tmp/ewu_axioms.lean`: exit 0. The exact quadratic identity,
  doubling law, exponential-type lemma, no-negative-double-pole theorem and main
  classification depend only on `propext`, `Classical.choice`, and `Quot.sound`.
  No `sorryAx`, added axiom or computation oracle occurs.
- `scripts/formal_tools.py index`: refreshed the generated indexes. The exact
  corpus search finds `canonical_or_negative_superpole` in the new module.
- `scripts/formal_tools.py lint`: the global gate has one unrelated pre-existing
  error: `GaloisForLFunctions.RHTower.CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion`
  is unreachable from its theorem-area umbrella. The new EWU module is reachable;
  no error points to it. That unrelated work was left untouched.
- `git diff --check`: passed.

No numerical experiment, web search, novelty audit, heartbeat increase, commit,
or push was used. Temporary proof and search files were removed after auditing.
