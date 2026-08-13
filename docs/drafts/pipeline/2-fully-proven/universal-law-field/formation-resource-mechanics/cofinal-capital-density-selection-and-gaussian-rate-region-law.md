# Cofinal capital-density selection and Gaussian rate-region law

- **ID:** ULF-FRM-4
- **Stage:** 2-fully-proven
- **Type:** GLOBAL FORMATION/PROPERNESS THEOREM FOR VARYING SOURCES
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL]`
  `[ASYMPTOTIC CAPITAL-DENSITY SELECTION] [EXACT GAUSSIAN RATE REGION]`
  `[FUNCTIONAL-EQUATION/RECOVERY NEUTRAL] [CLASSICAL RESOURCE-THEORY PARENT]`
  `[LEAN PENDING] [NOT RH]`
- **Statement:** A growing source can form growing independent target depth only when every target
  Rényi capital is bounded by source capital per formed copy. Vanishing source capital density
  forces target neutrality. For Gaussian quotient--fusion packets this bound is necessary and
  sufficient and gives exact quantitative convergence to synchronization.

## 1. Formation arrays

For each `n`, let

\[
 \mathcal E_n=(S_n;r_{n,0},r_{n,1})
 \tag{CDS.1}
\]

be a finite binary source experiment, let

\[
 \mathcal F_n=(X_n;p_{n,0},p_{n,1}),
 \tag{CDS.2}
\]

and let `d_n>=1`. An exact formation array is a sequence of Markov kernels

\[
 K_n:S_n\rightsquigarrow X_n^{d_n}
 \tag{CDS.3}
\]

such that

\[
 r_{n,i}K_n=p_{n,i}^{\otimes d_n}
 \qquad(i=0,1).
 \tag{CDS.4}
\]

For `0<alpha<1`, define extended Rényi capital

\[
 C_\alpha(u,v)=
 \begin{cases}
 -\log\sum_xu(x)^\alpha v(x)^{1-\alpha},&
   \sum_xu(x)^\alpha v(x)^{1-\alpha}>0,\\
 +\infty,&\text{otherwise}.
 \end{cases}
 \tag{CDS.5}
\]

Define source capital density

\[
 \rho_{n,\alpha}={C_\alpha(r_{n,0},r_{n,1})\over d_n}.
 \tag{CDS.6}
\]

## 2. Capital-density domination

### Theorem 2.1 -- intensive formation law

Every exact formation array satisfies, for all `n` and `0<alpha<1`,

\[
 \boxed{C_\alpha(p_{n,0},p_{n,1})\le\rho_{n,\alpha}.}
 \tag{CDS.7}
\]

The same law holds for every additive data-processing capital, including finite directed KL and
Jeffreys work.

#### Proof

Rényi overlap is monotone upward under Markov kernels, while tensor products multiply it. Thus

\[
 C_\alpha(r_{n,0},r_{n,1})
 \ge C_\alpha(p_{n,0}^{\otimes d_n},p_{n,1}^{\otimes d_n})
 =d_nC_\alpha(p_{n,0},p_{n,1}).
\]

Divide by `d_n`. Identical data-processing/additivity proof works for other capitals. QED.

### Theorem 2.2 -- vanishing-density selection

Fix one `alpha in (0,1)`. If

\[
 \rho_{n,\alpha}\longrightarrow0,
 \tag{CDS.8}
\]

then

\[
 \boxed{C_\alpha(p_{n,0},p_{n,1})\longrightarrow0.}
 \tag{CDS.9}
\]

If target experiment is independent of `n`, then

\[
 \boxed{p_0=p_1.}
 \tag{CDS.10}
\]

More generally, if a target parameter `v_n` obeys a source-normal coercivity law

\[
 C_\alpha(p_{v,0},p_{v,1})\ge c\,d(v,0)^q
 \qquad(c>0,q>0),
 \tag{CDS.11}
\]

then

\[
 \boxed{d(v_n,0)\le(\rho_{n,\alpha}/c)^{1/q}\longrightarrow0.}
 \tag{CDS.12}
\]

#### Proof

Equation `(CDS.9)` follows from `(CDS.7)`. If target is fixed, its capital is zero. Strict
Hölder equality for probability laws gives

\[
 \sum_xp_0(x)^\alpha p_1(x)^{1-\alpha}=1
 \iff p_0=p_1,
\]

proving `(CDS.10)`. Combine `(CDS.7)` and `(CDS.11)` for `(CDS.12)`. QED.

This is the varying-source form of global formation properness. Fixed-source properness is special
case `C_alpha(E_n)=constant`, `d_n->infinity`.

## 3. Exact Gaussian rate region

Let source be one-dimensional Gaussian shift `G_{b_n}` and target be Gaussian genesis packet
`Gamma(g_n)` with

\[
 Q_n=\|g_n\|^2.
 \tag{CDS.13}
\]

### Theorem 3.1 -- exact rate classification

There exists an exact formation

\[
 G_{b_n}\longrightarrow\Gamma(g_n)^{\otimes d_n}
 \tag{CDS.14}
\]

iff

\[
 \boxed{Q_n\le {b_n\over d_n}.}
 \tag{CDS.15}
\]

Consequently:

\[
 \boxed{limsup_n Q_n\le\limsup_n{b_n\over d_n}}
 \tag{CDS.16}
\]

whenever right side is an actual limit or both sides are interpreted through the pointwise bound.
In particular,

\[
 {b_n\over d_n}\longrightarrow0
 \quad\Longrightarrow\quad
 Q_n\longrightarrow0.
 \tag{CDS.17}
\]

If quotient--fusion equalizer has a quantitative gap

\[
 Q(v)\ge\lambda\|v\|^2\qquad(\lambda>0),
 \tag{CDS.18}
\]

then any formable displacement satisfies

\[
 \boxed{\|v_n\|\le\sqrt{{b_n\over\lambda d_n}}.}
 \tag{CDS.19}
\]

#### Proof

The product target has concatenated signal `(g_n,...,g_n)` of squared norm `d_nQ_n`. Exact
Gaussian Blackwell classification says `G_b` forms a Gaussian signal `m` iff `b>=||m||^2`.
This proves `(CDS.15)`. Remaining assertions are immediate. QED.

Unlike the general capital law, `(CDS.15)` is sufficient as well as necessary.

## 4. Testing prediction

Let `P_{e,n}` be equal-prior optimal Bayes error for one target genesis packet. Gaussian testing law
and `(CDS.15)` give

\[
 P_{e,n}=\Phi(-\sqrt{Q_n}/2)
 \ge \Phi\!\left(-{1\over2}\sqrt{{b_n\over d_n}}\right).
 \tag{CDS.20}
\]

### Corollary 4.1 -- vanishing density makes every one-copy observer blind

If `b_n/d_n->0`, then

\[
 \boxed{P_{e,n}\longrightarrow {1\over2}.}
 \tag{CDS.21}
\]

Thus capital-density selection predicts a fourth-organ effect: any formable Gaussian classifier
becomes asymptotically no better than guessing, even though each source experiment may itself
carry increasing total information.

## 5. Recovery and functional-equation conservation

### Theorem 5.1 -- capital density is description invariant

Suppose `E_n` is Blackwell-equivalent to a macropacket `M_n` through a statistic and one common
recovery kernel. Then

\[
 C_\alpha(E_n)=C_\alpha(M_n)
 \tag{CDS.22}
\]

and the capital density `(CDS.6)` is unchanged. If a functional-equation action is an experiment
isomorphism, it also preserves every `rho_{n,alpha}`. Neither operation can turn positive capital
density into vanishing density.

#### Proof

Data processing in both directions gives equality. Experiment isomorphism is a special case. QED.

### Corollary 5.2 -- sufficient formation saturates but does not select

For a sufficient macropacket of `d_n` iid descendants,

\[
 C_\alpha(M_n)=d_nC_\alpha(F_n),
 \tag{CDS.23}
\]

so

\[
 \rho_{n,\alpha}=C_\alpha(F_n).
 \tag{CDS.24}
\]

Unless target already tends to neutral, density does **not** vanish. Exact sufficient recovery is a
capital-saturating producer, not a selection producer.

This kills a plausible misuse of theta, binomial, Poisson, geometric, and other sufficient-sum
macropackets: their exact recovery proves information conservation, not critical selection.

## 6. Mechanism-level interpretation

The intensive object

\[
 \alpha\longmapsto\rho_{n,\alpha}
 \tag{CDS.25}
\]

is a capital-density profile. It separates roles which corpus routes repeatedly conflated:

| corpus phenomenon | formation meaning |
|---|---|
| hypertranscendental/prolongation rank | candidate independent depth `d_n`; not capital by itself |
| positive Gram or QFI | local target capital |
| recurrence/open history | can enlarge `d_n` without increasing observed capital proportionally |
| topology/admission | decides whether formation kernels exist and compose cofinally |
| sufficient recovery | preserves total capital exactly |
| functional equation | acts isometrically on capital profile |
| selection | requires capital density to vanish plus target coercivity |

This table is not a proof of cross-organ formation. It states exact typed obligations. A route only
enters theorem after producing `E_n`, `K_n`, and `d_n` before target specialization.

## 7. Hostile conjecture loops

1. **Unbounded source capital prevents selection -- false.** Total `C(E_n)` may diverge while
   `C(E_n)/d_n` tends to zero. Intensive density, not total budget, controls per-copy target.
2. **Unbounded prolongation rank implies selection -- false.** Rank supplies `d_n` only after a
   Markov formation theorem. Without `K_n`, dividing capital by rank is theatre.
3. **Sufficient recovery supplies vanishing density -- false.** It gives exact equality
   `(CDS.23)` and therefore constant target density.
4. **Functional equation halves density -- false.** Reversible action is an isometry.
5. **One scalar gives complete conversion -- false generally.** Rényi/KL bounds are necessary;
   exact sufficiency in this card is special to Gaussian shift chain.
6. **Vanishing density is already RH -- false.** A literal pre-zero source must still produce
   cofinal formation and a target coercivity/equalizer law identifying neutral displacement with
   critical selection.

## 8. Parent theory and significance audit

Abstract asymptotic distinguishability rates are occupied by Blackwell/Le Cam theory and resource
theories of state-pair distinguishability. The inequality `(CDS.7)` is standard data processing.
No external novelty claim is made.

The corpus-level advance is exact composition of:

1. growing source formations;
2. an intensive capital profile;
3. exact Gaussian quotient--fusion rate region;
4. quantitative equalizer convergence;
5. hypothesis-testing prediction;
6. proof that sufficient recovery and functional equation are density-neutral.

It converts the vague demand for a “source-native global formation theorem” into one falsifiable
analytic target:

\[
 \boxed{
 \text{construct }K_n, d_n\to\infty,
 \quad C_\alpha(E_n)=o(d_n),
 \quad C_\alpha(F_v)\gtrsim d(v,0)^q.}
 \tag{CDS.26}
\]

If all clauses are sourced before Xi specialization, selection follows automatically.

Primary parents:

- Blackwell comparison of experiments;
- Le Cam randomization/deficiency theory, <https://arxiv.org/abs/1605.03301>;
- Markov categories and sufficiency, <https://arxiv.org/abs/1908.07021>;
- asymmetric distinguishability resource theory, <https://arxiv.org/abs/1905.11629>;
- symmetric distinguishability resource theory, <https://arxiv.org/abs/2102.12512>.

## 9. Lean gate

No Lean file was written or built in this research pass. Future formalization should first certify
finite sequence form of `(CDS.7)`, then Gaussian iff `(CDS.15)`, then quantitative bound
`(CDS.19)`. Stage 3 remains forbidden until closed declarations are wired into universal-law
umbrella.
