# Actual inversion phase energy and original Fourier reduction

- **Stage:** 1-in-progress
- **Type:** POSITIVE SOURCE PHASE ENERGY LAW
- **Goal:** Identify the actual inversion loss as explicit phase-weighted displacements, reduce it using the original Fourier eigenspace constraint, and connect it to physical source energy.

## Conjecture and dependency-closed paper proof

The audited cycle45 kernel is the normalized average of actual unitary deck motions `W_abc = chi(r*b-s*(a+c))*U_(U(a)L(b)U(c))`. Its Gram form is `||C_rs v||²`. Expanding each `||v-W_abc v||²`, unitarity makes both squared terms `||v||²`; the complete normalized cross term is the actual Gram form. Thus the triple average divided by two equals `||v||²-||C_rs v||²`.

Stronger conjecture: the loss splits exactly into the missing upper character energy `||v-P_s v||²` and the missing lower character energy `||P_s v-Q_-r P_s v||²`. This follows from orthogonal projection and the proved inversion conjugacy. For each original Fourier coefficient `a_n(y)`, the already proved relation `P_(n mod L) a_n=a_n` removes the first term. The remaining loss is exactly the normalized average of `||a_n-chi(r*b)*U_L(b) a_n||²/2`. Summation should identify this with the original slice mass minus the physical lower-character slice mass; convergence must come from the original Parseval identities.

These identities introduce no phase or spectral endpoint hypothesis. The final full-domain mass comparison with four times physical gradient remains a target, not an input.

## Corpus evidence

Revalidated both cycle45 source hashes unchanged. Explicit OR search for twisted displacement, phase defect, norm subtraction, and Dirichlet form reached180 declarations in52 modules (`/tmp/selberg_phase48_corpus.json`). Read the actual finite regular Reynolds energy proof and character projection self-adjointness/completeness; inspect graph Dirichlet polarization and coherent-history fibre energy as cross-topic mechanisms. Their abstract spectral-gap or fibre-response premises are not Maass inputs and will not be assumed.

## Gates

- [x] Source revalidation, explicit OR corpus discovery, and paper conjectures.
- [ ] Full actual triple phase-displacement identity.
- [ ] Exact projection-loss decomposition and original Fourier single-block reduction.
- [ ] Original physical mass/convergence identification and next quantitative source estimate.
- [ ] Scratch/source checks, targeted final audits, complete axiom/index/wiring/lint checks.
