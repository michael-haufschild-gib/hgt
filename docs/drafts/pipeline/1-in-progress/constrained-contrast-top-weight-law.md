# The constrained-contrast top-weight law: `θ_i = S_i/S_{i+1} ↗ 1`, uniformly above `8/11`

- **ID:** `constrained-contrast-top-weight-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, exact finite-dimensional)
- **Scientific status:** `[PAPER-PROVED TOP-WEIGHT LAW]`
  `[DEPTH-UNIFORM CENTER CONSEQUENCE WITHDRAWN]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE — NOVELTY UNVERIFIED]` `[NOT AN RH PROOF]`
- **Serves:** `constrained-prolate-weil-toeplitz-schur-law.md` (`WT11`, `WT17`),
  `constrained-prolate-two-mode-ground-state.md`, and any growing-depth version of the
  constrained-prolate lane.
- **Statement (corrected scope — see §0):** the top-weight sequence
  `θ_i = Q_i/Q_{i+1}` is **strictly increasing**, hence **uniformly bounded below by
  `θ_0 = 8/11`**, and **tends to `1`**. The formerly claimed depth-uniform center-value
  consequence is withdrawn in §5.2; only its fixed-depth version is currently proved.

## 0. SCOPE CORRECTION, made before this card was reported anywhere

The closed form itself is **already in the corpus** and I initially claimed it as new. It is
`constrainedProlateHermiteTheta` in
`formal/GaloisForLFunctions/RHTower/ConstrainedProlateHermiteContrast.lean:126`, whose docstring
already reads *"The limiting secular root `theta_k = Q_k/Q_{k+1}`"*, together with
`constrainedProlateHermiteTheta_mem_Ioo` (`0 < θ_k < 1`), `_zero = 8/11`, `_one = 176/211`, and the
contrast vectors `constrainedProlateHermiteContrast k j` — which are my `w^(i)` in a different
normalization (theirs `-a_j` for `j ≤ k` and `S_k/a_{k+1}` at `k+1`; multiply by `-a_{k+1}` to get
mine).

**What is genuinely absent from the corpus, and is what this card now claims:**

1. `θ_i` is **strictly increasing** (the tree has only `0 < θ_i < 1`);
2. hence the **uniform floor** `θ_i ≥ 8/11` — which is the whole point, because `θ_i > 0` alone is
   useless for a growing depth;
3. `θ_i → 1`;
4. ~~the resulting **depth-uniform** center-value bound `(8)`~~ — withdrawn after hostile audit:
   the displayed triangle inequality omitted a growing evaluation/weighted-`ell^1` norm.

Sections 3 and the verification below are retained as a derivation of the existing definition, not
as a claim of novelty.

## 1. Why this was asked

The corpus records `θ_0 = 8/11` and `θ_1 = 176/211` as two numbers
(`constrained-prolate-weil-toeplitz-schur-law.md`, `(WT11)`), with no general law. A growing-depth
version of that lane needs the weights uniformly in `i`, and there was a live worry that they
**decay**: the limits themselves satisfy `a_j² = √2·C(4j,2j)/16^j ~ 1/(√π √j) → 0`, so it was not
clear that the top coefficient stays bounded away from zero. The law below settles it: it does,
and in fact the weight increases to `1`.

## 2. Setup

Let `e_j = h_{4j,λ}` be the fixed even prolate modes on the Fourier-eigenvalue-`+1` line, and let
`ℓ_j = ∫ e_j` be the constraint coordinates, with the prolate-to-Hermite limits

```text
ℓ_j -> a_j,     a_j² = √2 · C(4j,2j)/16^j,      a_0 = 2^(1/4),  a_1 = √3·2^(-5/4).
```

Put `S_k = Σ_{j=0}^{k} a_j²`. The constrained contrasts are defined by

```text
V_i = span{e_0,...,e_{i+1}} ∩ a^perp,     dim V_i = i+1,
g_i = the unit vector of V_i orthogonal to V_{i-1}      (V_{-1} = 0).
```

`g_0` is the CCM two-mode seed `(a_1 e_0 - a_0 e_1)/√(a_0²+a_1²)` in the limit.

## 3. The law

**Theorem.** Up to sign, `g_i` is the normalization of

```text
w^(i)_j = a_j a_{i+1}   (j ≤ i),      w^(i)_{i+1} = -S_i,                    (1)
```

with

```text
||w^(i)||² = S_i S_{i+1},                                                     (2)
```

so the squared top-mode weight is

```text
θ_i := (w^(i)_{i+1})² / ||w^(i)||² = S_i / S_{i+1} = 1 - a_{i+1}²/S_{i+1}.    (3)
```

**Proof.** Three checks on `(1)`.

*It satisfies the constraint.*
`w^(i) · a = a_{i+1} Σ_{j≤i} a_j² - S_i a_{i+1} = a_{i+1} S_i - S_i a_{i+1} = 0.`

*It is orthogonal to `V_{i-1}`.* Any `v ∈ V_{i-1}` lies in `span{e_0,...,e_i}`, so `v_{i+1} = 0`,
and satisfies `Σ_{j≤i} a_j v_j = v·a = 0`. Hence
`w^(i) · v = a_{i+1} Σ_{j≤i} a_j v_j = 0.`

*Its norm.*
`||w^(i)||² = a_{i+1}² Σ_{j≤i} a_j² + S_i² = a_{i+1}² S_i + S_i² = S_i(a_{i+1}² + S_i) = S_i S_{i+1}.`

Since `V_i` has dimension `i+1` and `V_{i-1}` dimension `i`, the orthogonal complement is a line,
so `g_i = w^(i)/||w^(i)||` up to sign. Formula `(3)` follows. `∎`

### Verification against the two recorded values

`q_j = C(4j,2j)/16^j`: `q_0 = 1`, `q_1 = 6/16 = 3/8`, `q_2 = 70/256 = 35/128`. So
`S_1 = √2·11/8`, `S_2 = √2·211/128`, and

```text
θ_0 = 1 - a_1²/S_1 = 1 - (3/8)/(11/8) = 8/11,
θ_1 = 1 - a_2²/S_2 = 1 - (35/128)/(211/128) = 176/211.
```

Both match `(WT11)` exactly. The law reproduces the only two values the corpus had.

## 4. Monotonicity and the limit

From `(3)`, `θ_i = 1 - a_{i+1}²/S_{i+1}` with every `a_j² > 0`, so `θ_i` is strictly increasing in
`i` and `θ_i < 1`. The central binomial asymptotic `C(2m,m) ~ 4^m/√(π m)` at `m = 2j` gives

```text
q_j ~ 1/√(2π j),      a_j² ~ 1/(√π √j),      S_k ~ 2√(k/π),                   (4)
```

hence

```text
a_{i+1}²/S_{i+1} ~ [1/(√π √i)] / [2√(i/π)] = 1/(2i),
θ_i = 1 - 1/(2i) + o(1/i)  ->  1.                                             (5)
```

**Uniform bound.** Since `θ_i` increases from `θ_0 = 8/11`,

```text
8/11 ≤ θ_i < 1   for every i ≥ 0.                                             (6)
```

The worry that the top weight decays with depth was therefore exactly backwards: the *limits*
`a_j²` decay like `j^{-1/2}`, but the *weight* is a ratio of their partial sums, and partial sums
of a `j^{-1/2}` sequence grow, so the ratio tends to one.

## 5. Consequences

### 5.1 The leakage law at every depth

`η_i = ⟨B_λ g_i, g_i⟩ = Σ_j (w^(i)_j)² d_j / ||w^(i)||²`. Because the fixed-mode Fuchs hierarchy
separates rungs by `d_{j+1}/d_j ~ λ^8`, the top term dominates and

```text
η_i = θ_i d_{i+1} (1 + O(λ^(-8))).                                            (7)
```

For `i = 0, 1` this is `(WT11)`; `(7)` is its general form, with the constant now identified.

### 5.2 Center-value bound: fixed depth only

The zero-integral constraint and the evaluation identity `ℓ_j = χ_{4j} e_j(0)` give, for any
normalized constrained contrast `g = Σ_j c_j e_j`,

```text
g(0) = Σ_j c_j e_j(0) - Σ_j c_j χ_{4j} e_j(0) = Σ_j c_j (1 - χ_{4j}) e_j(0),
1 - χ_{4j} = d_j/(1 + χ_{4j}),
```

The previous version concluded `|g(0)| <=C max_j d_j` with an absolute `C`.  That step is invalid:
normalization of `(c_j)` controls its `ell^2` norm, not

```text
sum_j |c_j e_j(0)|.
```

At fixed depth this sum is finite and gives a constant depending on `i`; hence `(7)` and `(6)`
only imply

```text
|g_i(0)| <=C_i*eta_i.                                                         (8)
```

An absolute constant would follow from a uniform weighted evaluation estimate such as

```text
sum_(j<=i+1) d_j^2*|e_j(0)|^2 <=C*d_(i+1)^2
```

or from an equivalent uniform leakage-ratio plus evaluation law.  Neither follows from the
top-weight floor and neither is proved here.  Thus this card does not yet supply the center input
for a growing-depth `(WT17)`.

## 6. Honest scope

- The law is a statement about the **limiting** coefficients `a_j`. Transferring it to the actual
  `ℓ_j(λ)` at depth `i` needs prolate-to-Hermite convergence `ℓ_j → a_j` for `j ≤ i+1`. CCM supply
  that only for `j = 0, 1`. For **fixed** depth it is finitely many classical limits; for a
  **growing** depth `i = i(λ)` it needs a uniform-in-`j` version that is not in
  Slepian/Fuchs/Dunster/CCM. That is the remaining input, and `(6)` removes the *other* worry
  (weight decay) that would have made growing depth hopeless on its own.
- `(7)` uses the fixed-mode Fuchs hierarchy, which is itself a fixed-`j` statement. A growing-depth
  version needs uniform-in-`j` Fuchs up to the Slepian plunge index `n ≈ 4λ²`, i.e. depth
  `i ≪ λ²`.
- Nothing here bears on RH. It is an exact finite-dimensional law about a constraint geometry.

## 7. Novelty audit

- **Parent overlap.** Larger than I first thought, and stated in §0: the closed form, the
  contrast vectors, `0 < θ_i < 1`, and both numerical values are already formalized in the tree.
  The construction is Gram–Schmidt against one linear constraint, a standard operation.
- **Non-parent residue.** Strict monotonicity of `θ_i`; the uniform floor `θ_i ≥ 8/11`; and the limit
  `θ_i → 1`. The formerly claimed depth-uniform center-value bound is not part of the residue.
  The monotonicity rests on the exact
  ratio
  `q_{j+1}/q_j = (4j+1)(4j+3)/[4(2j+1)(2j+2)] = (16j²+16j+3)/(16j²+24j+8) < 1`,
  which makes `q` strictly decreasing and hence `q_{k+1}/Q_{k+1}` strictly decreasing.
- **Literature.** The object (zero-integral constrained contrasts against the Fourier-`+1` prolate
  line, with `a_j² = √2 C(4j,2j)/16^j`) is specific to the CCM route and does not appear in the
  PSWF literature, so a direct collision is unlikely. Grade stays `[NOVELTY UNVERIFIED]`.
- **Significance.** Modest and instrumental. It removes one of the two named obstacles to a
  growing-depth constrained-prolate theorem and supplies the exact constant that theorem needs.

## Gates

- [x] closed form `(3)` re-derived by explicit orthogonal vector (already in tree — see §0)
- [x] reproduces both recorded values `8/11`, `176/211` (already in tree)
- [x] monotonicity and limit `(5)`, uniform floor `(6)` — **the residue**
- [ ] depth-uniform center-value bound `(8)` — withdrawn; requires a uniform weighted evaluation
      or leakage-ratio theorem
- [ ] independent audit (Codex)
- [ ] uniform-in-`j` prolate-to-Hermite `ℓ_j → a_j` (the remaining input for growing depth)
- [ ] uniform-in-`j` Fuchs hierarchy up to the plunge index
- [x] **Lean: the residue is formalized** in
      `formal/GaloisForLFunctions/RHTower/ConstrainedProlateTopWeightUniform.lean`, registered in
      the `GaloisForLFunctions.RHTower` umbrella, lint passes, axiom-clean:
      `constrainedProlateHermiteWeightSum_mono`,
      `constrainedProlateHermiteWeightSum_ge_eleven_div_eight`,
      `constrainedProlateHermiteTheta_ge_eight_div_eleven` (**the depth-uniform floor `θ_k ≥ 8/11`**),
      `constrainedProlateHermiteWeight_ge_inv` (`C(4j,2j)/16^j ≥ 1/(4j)`, from
      `Nat.four_pow_le_two_mul_self_mul_centralBinom` at argument `2j` — no asymptotics),
      `constrainedProlateHermiteWeightSum_ge_harmonic`,
      `tendsto_constrainedProlateHermiteWeightSum_atTop`, and
      `tendsto_constrainedProlateHermiteTheta_one` (**`θ_k → 1`**).
      Note the Lean proof of the floor avoids monotonicity of `θ` entirely: for `k ≥ 1` it uses
      `Q_k ≥ 11/8` and `q_{k+1} ≤ 1/2` to get `θ_k ≥ 11/15 > 8/11`, and `k = 0` is the exact value.
      That is cleaner than the paper route through the binomial ratio.

## 8. Both parity sectors, unified

The negative compressed-Fourier sector runs over prolate indices `4j + 2` and its recorded constants
are `8/13` and `5/13` (`2-fully-proven/new_scientific_knowledge/constrained-prolate-fourier-parity-floor-separation.md`,
formalized as `ccm_negativeSector_hermite_weight_eq`).  Those are the depth-zero values of the
**same** law: writing

```text
w(m) = C(2m,m)/4^m,
```

the positive sector's weight is `w(2j)` and the negative sector's is `w(2j+1)`, so both are the
even and odd subsequences of one central-binomial sequence.  Checking the recorded values:
`w(1) = 1/2`, `w(3) = 5/16`, and `(1/2)/((1/2)+(5/16)) = 8/13` exactly.

`formal/GaloisForLFunctions/RHTower/ProlateParityWeightUniform.lean` proves the three facts that
sequence needs — `centralBinomWeight_pos`, `centralBinomWeight_le_half` (`w m ≤ 1/2` for `m ≥ 1`),
`centralBinomWeight_ge_inv` (`w m ≥ 1/(2m)`, from
`Nat.four_pow_le_two_mul_self_mul_centralBinom`) — records the identification
`constrainedProlateHermiteWeight j = centralBinomWeight (2j)`, and gives the negative sector the
same two depth-uniform statements the positive sector has:

```text
negativeProlateHermiteTheta_zero          :  θ⁻_0 = 8/13
negativeProlateHermiteTheta_ge            :  8/13 ≤ θ⁻_k   for EVERY k
tendsto_negativeProlateHermiteTheta_one   :  θ⁻_k → 1
```

The floor proof for `k ≥ 1` gives the stronger `13/21`, and `13/21 > 8/13` by exactly one unit:
`13·13 = 169 > 168 = 8·21`.  Axiom-clean, in the umbrella, lint green.

**So the depth-uniform top-weight law now holds in both parity sectors, with the same mechanism:
the individual Hermite weights decay like `m^{-1/2}`, but the top weight is a ratio of partial
sums of a nonsummable sequence, so it increases to one.**

## Log

- 2026-07-27 (Claude): derived while settling a worry I had raised myself — that the top-mode
  weight might decay with depth and kill any growing-depth version of the Toeplitz–Schur lane. The
  worry was backwards; the weight increases to one.
- 2026-07-27 (Claude): **self-caught duplication before reporting.** Grepping the Lean tree (my own
  rule: grep the statement, not the gate) showed the closed form and both values were already
  formalized. Card rewritten to claim only monotonicity, the uniform floor `8/11`, the limit `1`,
  and the depth-uniform center-value bound. This is the first time today the rule caught a
  duplication *before* the work was reported rather than after.
