# Response to major-revision review

## Outcome

Manuscript now gives one coherent arithmetic--spectral classification. It retains exact
finite-period result needed for mathematical depth and directly constructs missing infinite-mode
object. Quantifiers cover:

1. every nonempty finite upper-half-plane period tuple;
2. every finite section of every ambient period family;
3. every ambient index set, including uncountable sets;
4. every positive real summability exponent;
5. every occupation sector containing all one-particle configurations;
6. every admissible finite Weierstrass genus;
7. every finite-mode exhaustion, newly adjoined mode, and pair of admissible genera.

## Arithmetic classification

For every finite tuple,

\[
G_\tau\text{ is differentially algebraic}
\iff
\dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}\{1,\tau_i\}=2,
\]

and rank at least three is exactly hypertranscendental phase. Same equivalences hold for
logarithmic derivative. For arbitrary ambient family, rank-three obstruction graph decides every
finite section. Its absence is equivalent to one rational affine line containing whole family.
This answers non-rational-period question, including non-rational differentially algebraic
exceptions such as \((i,1+i)\).

Proof has two exact mechanisms:

- augmented rank two clears denominators and reduces by simultaneous multiplication identity to
  Kato’s common-nome phase;
- augmented rank at least three contains two-period seed whose elliptic orbit obstruction is
  hypertranscendental; coface differences propagate obstruction to every higher order.

## Infinite spectral law

For arbitrary \(\Omega\subset\mathbb N^{(A)}\) containing each \(\delta_a\),

\[
\sum_{\nu\in\Omega}|p^\nu|^\sigma<\infty
\iff
\sum_a|p_a|^\sigma<\infty
\qquad(\sigma>0).
\]

Proof is sharp sandwich: one-particle sector embeds into \(\Omega\), and \(\Omega\) embeds into full
bosonic occupation space. Full bosonic mass is computed exactly as directed supremum of finite
Euler products. No named statistics receives special treatment.

## Infinite analytic object

Manuscript defines actual infinite-mode canonical determinant:

\[
\mathcal D_{\Omega,g}(x)=\prod_{\nu\in\Omega}E_g(xp^\nu).
\]

At every genus satisfying \(\sum_a|p_a|^{g+1}<\infty\), product converges locally uniformly on
\(\mathbb C\) and is entire for every sector \(\Omega\). For full bosonic sector:

- finite nome sets converge as inclusion-directed net;
- adjoining any distinguished nome gives exact tower and coface laws;
- every higher admissible genus differs by exponential of explicit finite polynomial of
  absolutely convergent occupation moments;
- every admissible genus has identical zero set.

## Physics scope

Diagonal multiplicative second quantization gives exact operator law:

\[
\Gamma_\Omega(P)\in\mathcal S_\sigma
\iff
P\in\mathcal S_\sigma
\qquad(\sigma>0).
\]

With \(\varepsilon_a=-\log|p_a|\), same statement gives equality of one-particle and many-body
Hagedorn inverse-temperature boundaries. Manuscript explains concrete use for:

- differential ODE obstruction for finite integrable-model and index blocks;
- infinite oscillator and Kaluza--Klein towers;
- generalized exclusion sectors;
- regularized one-loop determinants;
- infinite limits of elliptic-gamma partition blocks.

It states boundary of implication: results supply exact special-function and analytic
classifications after model weights are identified; they do not compute model-specific entropy,
spectrum, duality, or full dynamical integrability.

## Correctness repairs

- Integrated finite arithmetic classification and actual infinite determinant as independent
  nome-family invariants, without claiming differential classification of infinite limit.
- Removed every unproved parity-normalized finite-gamma limit.
- Replaced ratio scheme law by multiplicative identity valid at zeros.
- Restricted infinite “multiple elliptic gamma” terminology to canonical primary-factor block
  underlying standard finite hierarchy.
- Distinguished equality of convergence spectra from equality of partition values.
- Stated arbitrary-index sums and products as unordered finite-subset nets.
- Added maximality counterexample when one-particle retention is removed.
- Limited priority language to exact theorem suite.

## Final claim ledger

| Manuscript claim | Mathematical support |
|---|---|
| Exact finite arithmetic dichotomy | rational-affine multiplication reduction plus rank-three elliptic orbit obstruction |
| Every finite section of arbitrary family | rank-three obstruction graph and affine-line equivalence |
| Non-rational exceptional phase | explicit augmented-rank-two example outside rational ray |
| Exact full-bosonic mass | finite geometric identity plus directed finite-support exhaustion |
| Statistics-independent threshold | one-particle/full-boson sandwich |
| Equal critical exponent and Hagedorn boundary | equality for every positive exponent |
| Entire determinant for every sector | uniform primary-factor bound plus exact integer threshold |
| Enumeration-free finite-mode convergence | dominated convergence for unordered products |
| Exact coface recursion | occupation decomposition \(\mathbb N^{(\{\ast\}\sqcup B)}\cong\mathbb N\times\mathbb N^{(B)}\) |
| Exact scheme change | primary-factor identity plus absolutely convergent occupation moments |
| Same zero set | nonvanishing exponential scheme factor |
| Schatten preservation | diagonal singular values indexed by occupation configurations |
