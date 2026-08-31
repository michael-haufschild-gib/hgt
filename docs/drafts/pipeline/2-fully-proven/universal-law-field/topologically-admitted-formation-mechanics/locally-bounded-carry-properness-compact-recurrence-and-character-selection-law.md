# Locally bounded carry properness, compact recurrence, and character selection

- **ID:** ULF-TAFM-9
- **Stage:** 2-fully-proven
- **Type:** THEOREM PACKAGE
- **Source:** ULF-TAFM Laws VIII, XII, XIII; frontier gates `COF + ORIENT + COMP`
- **Status:** dependency-closed paper proof; Lean formalisation complete

## 1. Result

Local boundedness of lattice-carry traffic in a compact phase topology annihilates every real
formation character. This remains true when every group element uses a different invariant
probability system, gauge potential, and integer carry.

The mechanism is not continuity of one global potential. It is the fusion of three laws:

1. compensated-lift recovery converts carry traffic into a bound on real current;
2. compact phase recurrence produces returns at arbitrarily large word length;
3. an additive real character grows linearly on those same words.

Therefore a nonzero real current is incompatible with a uniform traffic ceiling on any fixed
phase neighborhood. Equivalently, nonneutrality has a compulsory, gauge-independent properness
signature: traffic diverges at least linearly along every cofinal family of compact-phase returns.

## 2. Setting

Let `A` be an additive group. Let `K` be a compact additive commutative group equipped with a
translation-invariant extended pseudometric `d`. Let

`i : A → K`, `χ : A → ℝ`

be additive homomorphisms. Fix a radius `r>0`, lattice period `L>0`, a traffic function
`τ : A → ℝ`, and a finite constant `C∈ℝ`.

The abstract current domination law is

`|χ(a)| ≤ L τ(a)` for every `a∈A`.                                      `(9.1)`

The local properness ceiling is

`d(i(a),0) ≤ 2r  implies  τ(a) ≤ C`.                                    `(9.2)`

For the intended compensated-lift model, each `a` may have its own finite invariant probability
system `(X_a, μ_a, T_a)`, integrable potential `u_a`, and integrable integer carry `k_a`, with

`u_a(T_a x)-u_a(x)+L k_a(x)=χ(a)` almost everywhere.                     `(9.3)`

Set `τ(a)=∫|k_a| dμ_a`. ULF-TAFM-8 gives

`χ(a)=L∫k_a dμ_a`, hence `|χ(a)|≤Lτ(a)`,

so `(9.1)` follows independently in each fibre. No common potential or cross-fibre gauge choice is
assumed.

## 3. Finite-cover return lemma

### Lemma 9.1 — bounded positive return

Let a finite set `F⊂K` have the property that its closed radius-`r` balls cover `K`. For every
`α∈K`, there is an integer `q` satisfying

`0<q≤|F|` and `d(qα,0)≤2r`.                                             `(9.4)`

### Proof

Place the `|F|+1` points

`0, α, 2α, …, |F|α`

in covering balls centered at points of `F`. Two points `iα,jα`, with `i<j`, share a center.
The triangle inequality gives `d(iα,jα)≤2r`. Translation invariance gives

`d((j-i)α,0)=d(jα,iα)≤2r`.

Take `q=j-i`. Then `0<q≤|F|`. ∎

Compactness and `r>0` supply such a finite cover.

### Lemma 9.2 — cofinally large returns

For every `α∈K` and every positive integer `N`, there is an integer `n` satisfying

`n≥N` and `d(nα,0)≤2r`.                                                 `(9.5)`

### Proof

Apply Lemma 9.1 to `Nα`. It gives `q>0` with `d(q(Nα),0)≤2r`. Put `n=qN`.
Then `n≥N` and `nα=q(Nα)`, proving `(9.5)`. ∎

This argument handles finite-order and infinite-order phases uniformly. It does not require dense
cyclic image, metrizability beyond the chosen compact translation pseudometric, or a minimal
rotation theorem.

## 4. Quantitative properness law

### Theorem 9.3 — return traffic lower bound

Under `(9.1)`, for every `a∈A` and `n∈ℕ`,

`τ(na) ≥ n|χ(a)|/L`.                                                    `(9.6)`

### Proof

Additivity gives `χ(na)=nχ(a)`. Applying `(9.1)` to `na` gives

`n|χ(a)|=|χ(na)|≤Lτ(na)`.

Division by `L>0` proves `(9.6)`. ∎

Thus if `χ(a)≠0`, traffic grows at least linearly on *every* sequence of positive multiples of
`a`, and in particular on every return sequence supplied by Lemma 9.2.

## 5. Selection theorem

### Theorem 9.4 — locally bounded carry properness selects the neutral character

Assume `(9.1)` and `(9.2)`. Then

`χ=0`.                                                                  `(9.7)`

### Proof

Fix `a∈A`. For every positive integer `N`, Lemma 9.2 applied to `i(a)` gives `n≥N` with
`d(n i(a),0)≤2r`. Since `i` is additive,

`i(na)=n i(a)`,

so `(9.2)` gives `τ(na)≤C`. Theorem 9.3 then yields

`n|χ(a)|≤LC`.                                                           `(9.8)`

If `χ(a)≠0`, the left side is unbounded as `N`, and hence `n≥N`, tends to infinity, while the
right side is fixed. This contradicts `(9.8)`. Therefore `χ(a)=0`. Since `a` was arbitrary,
`χ=0`. ∎

### Corollary 9.5 — compensated-lift family selection

Suppose the fibrewise compensated lifts `(9.3)` exist and some compact-phase ball satisfies

`d(i(a),0)≤2r  implies  ∫|k_a| dμ_a≤C`.

Then `χ=0`.

### Proof

ULF-TAFM-8 supplies `(9.1)` with `τ(a)=∫|k_a|dμ_a`; apply Theorem 9.4. ∎

## 6. Gauge neutrality and exact obstruction

Replacing a fibre potential by `u_a+Lh_a` changes its carry by the coboundary

`k_a+h_a-h_a∘T_a`. Invariance preserves its mean. Therefore the lower bound

`τ(na)≥n|χ(a)|/L`

cannot be removed by adaptive integrable gauge changes. A gauge may redistribute positive and
negative traffic, but it cannot change the recovered mean current whose absolute value forces the
lower bound.

This isolates the exact obstruction left by the theorem:

- off-neutral character is possible only if every proposed source construction loses local
  traffic boundedness along compact-phase returns, loses finite invariant mass, or loses carry
  integrability;
- proving a local source-derived traffic ceiling is enough for selection; constructing one common
  global potential is not necessary.

## 7. Cross-organ meaning

This is one mechanism acting across structurally different route organs:

- **packet/carry organ:** open lifted history is measured by integer traffic;
- **spectral/character organ:** recovered real grade is the additive current `χ`;
- **compact recurrence organ:** closed phase observation repeatedly forgets arbitrarily long lifted
  word length;
- **selection organ:** bounded information loss near closed phase forbids a nonzero open grade.

The theorem therefore predicts a fourth-organ statement: any route producing an off-critical real
character on a compact prime phase must exhibit linear `L¹` carry blow-up on cofinal near-identity
source words. This prediction applies to adaptive route gauges, not only to a preselected potential.

## 8. Hostile audit

1. **Not a discrete-topology boundedness trick.** The controlled neighborhood is pulled back from
   compact phase through `i`; boundedness on a finite generating set is insufficient.
2. **No false density premise.** Lemma 9.2 uses only compactness and a finite cover. Applying the
   collision lemma to `Nα` is what makes return times cofinal.
3. **No common-gauge assumption.** Proof consumes only the fibrewise domination `(9.1)`.
4. **No reflected-pair loophole.** Selection is elementwise before functional-equation pairing;
   cancellation of two nonzero currents does not bound either traffic.
5. **No sign mistake.** Absolute current, not signed mean, drives `(9.6)`.
6. **Sharp scale.** Linear coefficient `|χ(a)|/L` follows directly from exact current recovery and
   cannot be improved without extra information about counterflow.
7. **Necessary escape chambers remain explicit.** Infinite measure, nonintegrable carry, or absence
   of a local family ceiling are not ruled out.
8. **No RH claim.** Result changes selection architecture by replacing one global-potential burden
   with a local source-properness burden. Critical-line selection still requires deriving that
   ceiling from arithmetic formation laws.

## 9. Dependency audit

- Lemma 9.1: finite pigeonhole principle, triangle inequality, translation invariance.
- Lemma 9.2: compact finite cover plus Lemma 9.1.
- Theorem 9.3: additivity, absolute-value homogeneity for natural multiples, `L>0`.
- Theorem 9.4: Lemma 9.2, Theorem 9.3, Archimedean unboundedness of natural numbers.
- Corollary 9.5: ULF-TAFM-8 probability current recovery and integral triangle inequality.

All dependencies are standard or already proved in the corpus. No RH, density, continuity,
zero-location, or unproved analytic premise is used.

## 10. Literature boundary

Neighboring ingredients include automatic continuity of measurable homomorphisms
<https://arxiv.org/abs/2206.02481>, bounded cocycle/coboundary rigidity
<https://arxiv.org/abs/1109.4322>, and bounded homomorphism theory
<https://arxiv.org/abs/1501.04923>. This theorem package uses the elementary compact-recurrence
mechanism and fuses it with exact lattice-carry recovery. No novelty criterion is imposed.

## Gates

- [x] 0 → 1: source topology, quantitative survivor, and hostile tests frozen
- [x] 1 → 2: dependency-closed proof of cofinal return, traffic blow-up, and selection
- [x] 2 → 3: Lean formalisation, including missing additive compact-return infrastructure
- [ ] 3 → 4: source application and literature comparison
