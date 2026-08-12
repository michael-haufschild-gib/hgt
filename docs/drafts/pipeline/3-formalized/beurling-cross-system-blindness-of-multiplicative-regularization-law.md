# Beurling cross-system blindness of multiplicative regularization

- **ID:** ULF-INV-1
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / FIRST NECESSITY AXIOM OF THE INVERSE THEORY
- **Source:** inversion of the corpus blindness theorem (`rh-producer-map-corpus.md` §17,
  `HTGeometry/MultiplicativeRegularizationBlind.lean`) from an internal limit statement into a
  cross-system statement about what the method can ever see
- **Statement:** Over the class of Mertens-normal Beurling systems, every convergent
  multiplicatively regularized limit of the prime log-jet Grams is a function of the normalizer
  alone — constant across systems — and therefore determines neither the zero set nor the system.
  Any finite pairing that detects zeros must consume input beyond Mertens-normal moment data.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [NECESSITY AXIOM N1] [CORPUS PARENT CITED]
  [NOT RH] [LEAN CERTIFIED]

## 1. Setting

A **Beurling system** \(\mathcal P\) is a sequence of generalized primes
\(1<p_1\le p_2\le\cdots\to\infty\); its generalized integers are the multiplicative semigroup they
generate (with multiplicity), \(\Lambda_{\mathcal P}\) its von Mangoldt function
(\(\Lambda_{\mathcal P}(n)=\log p\) on generalized prime powers \(n=p^k\), extended by \(0\)),
and \(\zeta_{\mathcal P}(s)=\prod_i(1-p_i^{-s})^{-1}\) where convergent.

Call \(\mathcal P\) **Mertens-normal** if

\[
S_{\mathcal P}(N):=\sum_{n\le N}\frac{\Lambda_{\mathcal P}(n)}{n}
=\log N+C_{\mathcal P}+o(1)
\qquad(N\to\infty).
\tag{INV.1}
\]

The rational primes are Mertens-normal (classical Mertens). The **prime log-jet Gram** of
\(\mathcal P\) at aperture \(N\) is the corpus's object

\[
H^{\mathcal P}_{k}(N)=\sum_{n\le N}\frac{\Lambda_{\mathcal P}(n)}{n}\,(\log n)^{k},
\qquad
H^{\mathcal P}(N)_{ij}=H^{\mathcal P}_{i+j}(N).
\tag{INV.2}
\]

A **multiplicative regularization** is a family \(c^{(N)}_k\in\mathbb R\) (arbitrary dependence on
\(k\) and the aperture) applied entrywise, \(H_{ij}\mapsto c^{(N)}_{i+j}H_{i+j}(N)\).

## 2. Leading structure

### Lemma 2.1

If \(\mathcal P\) is Mertens-normal then, with \(L=\log N\),

\[
H^{\mathcal P}_k(N)=\frac{L^{k+1}}{k+1}+O_k\bigl(L^{k}\bigr).
\tag{INV.3}
\]

#### Proof

Riemann–Stieltjes partial summation against (INV.1): writing
\(S(x)=\log x+C+\varepsilon(x)\) with \(\varepsilon(x)=o(1)\) and \(\varepsilon\) bounded,

\[
H_k(N)=\int_{1^-}^{N}(\log x)^k\,dS(x)
=\int_1^N\frac{(\log x)^k}{x}\,dx+\int_{1^-}^N(\log x)^k\,d(C+\varepsilon(x)).
\]

The first integral is \(L^{k+1}/(k+1)\). The second is, after integration by parts,
\((\log N)^k\varepsilon(N)-k\int_1^N(\log x)^{k-1}\varepsilon(x)\,dx/x
=o(L^k)+O_k(L^{k})\), using boundedness of \(\varepsilon\). QED.

## 3. Cross-system blindness

### Theorem 3.1 — the limit is a function of the normalizer alone

Let \(\mathcal P\) be Mertens-normal and let \(c^{(N)}\) be any multiplicative regularization such
that \(c^{(N)}_kH^{\mathcal P}_k(N)\) converges as \(N\to\infty\) for each \(k\), with some limit
nonzero. Then \(c^{(N)}_kL^{k+1}\) converges, say to \(\delta_k\), and

\[
\lim_{N\to\infty}c^{(N)}_kH^{\mathcal P}_k(N)=\frac{\delta_k}{k+1}.
\tag{INV.4}
\]

Consequently, for any two Mertens-normal systems \(\mathcal P,\mathcal P'\) and any regularization
under which both converge, the limit matrices are **equal**:

\[
\lim c^{(N)}\!\cdot H^{\mathcal P}(N)=\lim c^{(N)}\!\cdot H^{\mathcal P'}(N).
\tag{INV.5}
\]

#### Proof

By (INV.3), \(H_k(N)=L^{k+1}(1/(k+1)+O(1/L))\). If \(c^{(N)}_kH_k(N)\to\ell_k\) then
\(c^{(N)}_kL^{k+1}=c^{(N)}_kH_k(N)\cdot\bigl(1/(k+1)+O(1/L)\bigr)^{-1}\to(k+1)\ell_k=:\delta_k\),
and conversely \(c^{(N)}_kH_k(N)=c^{(N)}_kL^{k+1}\cdot(1/(k+1)+O(1/L))\to\delta_k/(k+1)\).
Both limits are functions of \((\delta_k)\) alone; (INV.5) follows since the same \(c^{(N)}\) fixes
the same \((\delta_k)\). (This is the cross-system form of the corpus's
`tendsto_mul_regularized`; the aperture calibration \(L=\log N\) is shared because both systems
satisfy (INV.1) with leading coefficient \(1\).) QED.

### Theorem 3.2 — the limit determines neither the zeros nor the system

There exist Mertens-normal Beurling systems \(\mathcal P\ne\mathcal P'\) with
\(\zeta_{\mathcal P}\ne\zeta_{\mathcal P'}\) and different zero sets, on which every convergent
multiplicative regularization takes identical limits. Concretely: let \(\mathcal P\) be the
rational primes and \(\mathcal P'\) the rational primes with the generator \(2\) replaced by any
\(\beta\in(1,\infty)\), \(\beta\ne2\). Then:

1. \(\mathcal P'\) is Mertens-normal.
2. On the common half-plane of convergence,

   \[
   \zeta_{\mathcal P'}(s)=\zeta(s)\,\frac{1-2^{-s}}{1-\beta^{-s}},
   \tag{INV.6}
   \]

   which extends meromorphically wherever \(\zeta\) does; the point \(s_0=2\pi i/\log 2\) is a
   zero of the factor \(1-2^{-s}\) and not a pole of \(1/(1-\beta^{-s})\) for
   \(\log 2/\log\beta\notin\mathbb Q\), while \(\zeta(s_0)\ne0\) (all zeros of \(\zeta\) lie in
   the critical strip or at negative even integers, and \(s_0\) is purely imaginary, nonzero).
   Hence \(s_0\) is a zero of \(\zeta_{\mathcal P'}\) and not of \(\zeta\): the zero sets differ.
3. Every convergent multiplicative regularization has the same limit on \(\mathcal P\) and
   \(\mathcal P'\) (Theorem 3.1).

#### Proof

Item 1: \(\Lambda_{\mathcal P'}=\Lambda-\log2\sum_k\delta_{2^k}+\log\beta\sum_k\delta_{\beta^k}\)
as measures on \((1,\infty)\), so

\[
S_{\mathcal P'}(N)=S_{\mathcal P}(N)
-\log2\!\!\sum_{2^k\le N}\!2^{-k}
+\log\beta\!\!\sum_{\beta^k\le N}\!\beta^{-k},
\]

and both corrections converge as \(N\to\infty\) (geometric series), so (INV.1) holds with a
shifted constant. Item 2: (INV.6) is the Euler-product manipulation on
\(\operatorname{Re}s>1\), and both sides continue; the factor's zeros are
\(s=2\pi ik/\log2\), its poles \(s=2\pi ik/\log\beta\); choosing \(\beta\) with
\(\log2/\log\beta\) irrational makes zeros and poles disjoint away from \(s=0\); \(\zeta\) is
zero-free and pole-free at \(s_0\). Item 3 is Theorem 3.1. QED.

### Corollary 3.3 — necessity axiom N1

Any finite pairing built from the prime log-jet source by entrywise (multiplicative)
regularization is constant on the Mertens-normal class and therefore carries no information about
the zero set of the underlying zeta function. Hence: **any theory whose pairing is finite,
positive, and zero-sensitive must consume structural input beyond Mertens-normal moment data** —
the pairing cannot factor through the multiplicative-regularization functor.

## 4. Hostile scope

- The internal blindness mechanism is the corpus's (`tendsto_mul_regularized`); Lemma 2.1 and the
  cross-system/Beurling formulation, the explicit comparison pair, and Corollary 3.3's necessity
  reading are what this card adds. If a corpus or literature source already states the
  cross-system form, this card demotes to BRIDGE — a search of the corpus docs found the internal
  form only (§17), and Beurling comparison arguments in the literature (Diamond; Zhang;
  Diamond–Montgomery–Vorhauer, who build far deeper oscillation examples than needed here) are
  cited as parents for the technique of varying the system.
- The theorem does not touch subtractive or nonlinear regularizations (closed separately by the
  corpus's §§20–22 within their families), and creates no positivity. Its role is axiomatic: it
  is the first entry of the specification the missing object must satisfy.
- \(\beta\) with \(\log2/\log\beta\) irrational exists trivially (any transcendental \(\beta\),
  or \(\beta=3\): \(\log2/\log3\) irrational since \(2^a=3^b\) has no nontrivial integer
  solutions — with \(\beta=3\) the system has a doubled prime \(3\), which Beurling systems
  permit (multiplicity is allowed); item 2's disjointness at \(s_0\) needs only
  \(2^{-s_0}=1\ne\beta^{-s_0}\), i.e. \(\log\beta/\log2\notin\mathbb Z\) at \(k=1\), true for
  \(\beta=3\).)

## Log

- 2026-08-09 — created as the first executed step of the inverse theory: corpus no-go inverted
  into a cross-system impossibility with explicit comparison pair, and read as necessity axiom N1.
- 2026-08-12 — fully formalized in Lean and promoted to stage 3.  Two new modules:
  `HTGeometry/BeurlingCrossSystemBlindness.lean` (Beurling systems, layer-cake Gram entries,
  cross-system blindness, zero-set separation) and `RHTower/BeurlingRationalPrimeSystem.lean`
  (the concrete pair).  51 declarations, all axiom-clean.

## Lean certification

Module: `formal/GaloisForLFunctions/HTGeometry/BeurlingCrossSystemBlindness.lean`
(wired into `GaloisForLFunctions.HTGeometry`; 38 declarations, all audited to
`[propext, Classical.choice, Quot.sound]`; no `sorry`, no added axiom).

A Beurling system is carried by the structure `System ι`: magnitudes `mag i ≥ 1`, nonnegative
weights, finitely many atoms below every threshold.  `System.mertens` is `S`, `System.jet k` is
`H_{k+1}`.  Mertens-normality is used in the *bounded* form `|S(x) − log x − C| ≤ M` for `x ≥ 1`,
which is weaker than (INV.1), so every theorem below is correspondingly stronger.

| Card statement | Lean name |
|---|---|
| Lemma 2.1, (INV.3) | `System.jet_sub_main_abs_le` — `\|H_{k+1}(N) − L^{k+2}/(k+2)\| ≤ 2M L^{k+1}` |
| Lemma 2.1, layer-cake form | `jetIntegral_sub_main_abs_le`, `integral_layer_main` |
| sum = Stieltjes integral | `System.jet_eq_jetIntegral`, `integral_layer_atom`, `System.mertens_sub` |
| Thm 3.1, normalized limit | `System.tendsto_jet_ratio` — `H_{k+1}(N)/L^{k+2} → 1/(k+2)` |
| Thm 3.1, (INV.4) | `tendsto_normalizer_of_tendsto_ratio` — `c·L^{k+2} → (k+2)ℓ`, compensation derived |
| Thm 3.1, (INV.5) | `regularized_jet_limit_eq_of_systems`, `tendsto_mul_cross_system` |
| Thm 3.2 item 1 | `mertensNormal_swapMertens`, `tendsto_geomTail`, `tendsto_geomCount` |
| Thm 3.2 item 2, (INV.6) | `hasProd_deletedEulerFactor`, `swappedZeta_eq_tprod` |
| Thm 3.2 item 2, zero split | `zeroSets_differ`, `cpow_two_genFreq`, `cpow_three_genFreq_ne_one`, `riemannZeta_genFreq_ne_zero` |
| Cor 3.3, N1 | `regularized_limit_const_on_family`, `regularized_limit_eq` |

Notes on the formal renderings.

- The Riemann-Stieltjes step of Lemma 2.1 is replaced by an exact layer-cake identity
  (`System.jet_eq_jetIntegral`): `(log t)^{k+1} = ∫_0^L (k+1)u^k [u < log t] du`, summed over the
  aperture.  The error term is proved in the sharper form `2M L^{k+1}` with the explicit constant,
  not merely `O_k(L^k)`.
- The comparison generator is `β = 3`, and the disjointness input is the card's own weakest
  sufficient condition: `log 3 / log 2 ∉ ℤ`, proved from `2 < 3 < 4`
  (`log_three_div_log_two_not_int`).
- `swappedZeta` is *defined* by the meromorphic formula `ζ(s)(1−2^{-s})/(1−3^{-s})`;
  `swappedZeta_eq_tprod` proves it agrees with the swapped Euler product on `Re s > 1`, which is
  exactly what (INV.6) asserts.  `riemannZeta_genFreq_ne_zero` runs the functional equation
  `riemannZeta_one_sub` at `1 − s₀` (real part `1`) and discharges the four factors: `Γ ≠ 0`,
  `(2π)^{-s} ≠ 0`, `cos(πs/2) ≠ 0` (its argument has nonzero imaginary part), `ζ ≠ 0` on `Re = 1`.

### The concrete comparison pair

Module: `formal/GaloisForLFunctions/RHTower/BeurlingRationalPrimeSystem.lean`
(wired into `GaloisForLFunctions.RHTower`; 13 declarations, all audited to
`[propext, Classical.choice, Quot.sound]`).

Both systems are built on the index type `ℕ` with magnitudes `max n 1`, so they share an aperture.

| Card statement | Lean name |
|---|---|
| `𝒫` = rational primes, Mertens-normal (§1, classical Mertens) | `rationalPrimeSystem`, `exists_rationalPrimeSystem_bound` |
| `𝒫'` = `2` deleted, `3` doubled | `swappedPrimeSystem` (`swapWeight`) |
| Thm 3.2 item 1, `𝒫'` Mertens-normal | `exists_swappedPrimeSystem_bound` |
| generator tail `∑_{q^k ≤ x} Λ(q^k)/q^k ≤ log q` | `genPow_tail_le`, `sum_inv_pow_le` |
| Thm 3.2, whole statement | `rationalPrime_swap_blindness` |

The Mertens-normality of the rational primes is discharged by the corpus's own elementary
`RHTower.Mertens.mertens_first` (`|∑_{d ≤ n} Λ(d)/d − log n| ≤ log 4 + 4`, no prime number theorem),
transferred from integer to real apertures by `abs_log_sub_log_floor_le`.  So §1's "classical
Mertens" citation is discharged inside the corpus rather than assumed.

`rationalPrime_swap_blindness` is the card's Theorem 3.2 in one statement: for every exponent, every
normalizer, and any two limits the normalizer produces on the two systems, the limits are equal,
`swappedZeta` vanishes at `s₀ = 2πi/log 2`, and `ζ(s₀) ≠ 0`.

**Card status: fully formalized.**  Every displayed statement of §§2–3 (Lemma 2.1, Theorem 3.1
including (INV.4)/(INV.5), Theorem 3.2 items 1–3 including (INV.6), Corollary 3.3) has an
unconditional Lean proof.  §4's "hostile scope" contains no theorem.
