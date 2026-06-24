# Finite Continuation, Infinite Boundary

## A synthetic research narrative connecting the ADE, Böttcher, Hurwitz, and `u₀` documents

**Status of this document:** synthetic research memo. It is not a replacement for the proof cards. It deliberately mixes three levels of assertion:

1. **Proved input** — statements recorded as proved in the uploaded cards.
2. **Analytical synthesis** — explanations of how the proved cards seem to fit together.
3. **Speculative bridges** — conjectures and connective tissue that may be false. These are explicitly labeled.

The central claim of the synthesis is this:

> The documents are all different views of one obstruction principle: a finite algebraic or differential constraint tries to turn local information into analytic continuation, finite branching, or rationally controllable singular data; the objects in the cards defeat that finite control by carrying too much boundary information — a natural boundary, an infinite dyadic monodromy group, or non-rational branch-tail data.

This is the story of **finite continuation versus infinite boundary**.

---

## 0. Source map

The uploaded documents fall into four clusters.

### A. The bounded-jet ADE / natural-boundary criterion

- `ade-boundary-hinf-ht.md` proves, in its sharpened form, that if a holomorphic function on the disk satisfies a minimal irreducible algebraic differential equation of order `n` and the order-`n` jet
  
  ```text
  f, f′, …, f^(n) ∈ H^∞(D)
  ```
  
  then the unit circle is **not** a natural boundary. Equivalently, a function with a natural boundary and bounded order-`n` jet is hypertranscendental.

The philosophical role of this card is that a differential-algebraic equation is a local continuation engine. If the jet stays bounded up to the boundary, the engine can be anchored near a good boundary point and pushed across.

### B. Quadratic inverse Böttcher coordinates and Nguyen Q6.2

- `q62-bottcher-independence-natural-boundary.md` proves the connected nonexceptional case: for distinct `c₁,c₂ ∈ M \ {0,-2}`, the inverse Böttcher coordinates `φ_{c₁}` and `φ_{c₂}` are algebraically independent.
- `bottcher-exact-pruefer-monodromy.md` proves the exact disconnected monodromy theorem: for `c ∉ M`, the scalar monodromy image of `φ_c` on `Ω_c = C \ K_c` is exactly the Prüfer `2`-group `μ_{2^∞}`.
- `q62-both-disconnected.md` uses that exact monodromy to prove algebraic independence when both parameters are disconnected and distinct.
- `q62-bottcher-independence-n2-all-parameters.md` assembles connected, disconnected, and mixed cases into the full quadratic `n=2` nonexceptional answer to Nguyen Q6.2: if `c₁ ≠ c₂` and `c₁,c₂ ∉ {0,-2}`, then `φ_{c₁}` and `φ_{c₂}` are algebraically independent over `C(z)`.
- `q62a-bottcher-independence-hyperbolic.md` is the earlier/calibrated hyperbolic connected stratum, now subsumed by the all-connected card but still useful as a clean subcase.

The philosophical role of this cluster is that algebraic dependence would force either forbidden continuation through a Julia boundary point or finite absorption of an infinite dyadic monodromy group.

### C. The monomial-fiber velocity `u₀` versus Böttcher coordinates

- `u0-phi-independence.md` proves the connected case: the lacunary monomial-fiber velocity
  
  ```text
  u₀(z)=Σ_{n≥0} 2^{-(n+1)} z^{-(2^{n+1}-1)}
  ```
  
  is algebraically independent from `φ_b` over `Qbar(b,z)` for `b ∈ M \ {0,-2}`.
- `u0-phi-independence-disconnected.md` proves the disconnected case using a Green-crossing lemma.
- `u0-phi-independence-all-parameters.md` assembles both into the all-nonexceptional theorem: for every `b ≠ 0,-2`, `u₀` and `φ_b` are algebraically independent over `Qbar(b,z)`.

The philosophical role of this cluster is that a failed degeneration in the two-parameter Böttcher problem becomes a positive mixed-object theorem. The “tangent leak” `u₀` cannot be algebraically generated from any nonexceptional Böttcher coordinate.

### D. Hurwitz zeta quadratic shift-ladder independence

- `hurwitz-quadratic-n2-density-shadow.md` proves the first nonlinear `N=2` obstruction: for `Re(s)>1`, `s∉Z`, the triple
  
  ```text
  ζ(s,a), ζ(s+1,a), ζ(s+2,a)
  ```
  
  satisfies no nonzero `C(a)`-polynomial relation of total degree at most two.
- `hurwitz-quadratic-all-n-tail-independence.md` upgrades this to every finite shift ladder
  
  ```text
  { ζ(s+k,a) }_{0≤k≤N}
  ```
  
  again at total polynomial degree at most two.

The philosophical role of this cluster is that even when leading branch exponents create apparent algebraic collisions, the regular branch tails remember noninteger harmonic sums that rational coefficients cannot interpolate.

---

## 1. The common mechanism: finite constraints as continuation machines

The most useful way to read the collection is not as a list of unrelated results but as a program.

A finite algebraic relation

```text
P(z, F₁(z), …, F_m(z)) = 0
```

or a finite algebraic differential equation

```text
P(z, f, f′, …, f^(n)) = 0
```

is not merely an identity. It is a mechanism for controlling analytic continuation.

Depending on the context, it gives one of three kinds of control.

### 1.1 Algebraic continuation control

If all functions except one are already analytic near a point, an algebraic relation can make the remaining function algebraic over the analytic ones. Away from leading-coefficient and discriminant bad loci, the algebraic implicit function theorem then supplies local analytic branches. This is the engine in:

- the connected Böttcher independence theorem;
- the connected and disconnected `u₀ ⊥ φ_b` theorems;
- the connected part of the all-parameter Nguyen Q6.2 theorem.

In each case the contradiction is similar:

1. One object has a forbidden boundary, such as a Julia boundary or the unit circle natural boundary of `u₀`.
2. The other object is analytic on a domain crossing that boundary.
3. A finite algebraic relation would continue the forbidden object through a generic crossing point.
4. That continuation contradicts the boundary obstruction.

### 1.2 Monodromy control

A finite algebraic relation also forces finite-degree behavior under analytic continuation. If a loop changes one coordinate by many distinct scalar multipliers while fixing the others, then the relation would create too many roots of a polynomial of fixed degree.

This is the engine in the disconnected Böttcher arguments. In the disconnected quadratic locus, the exact monodromy of `φ_c` is not merely infinite; it is the full dyadic Prüfer group

```text
μ_{2^∞} = { exp(2πir) : r ∈ Z[1/2] }.
```

A loop around a depth-`n` Cantor cylinder multiplies `φ_c` by `exp(2πi/2^n)`. Choosing `2^n` larger than the degree of a supposed algebraic relation forces a degree contradiction.

### 1.3 Differential continuation control

A finite algebraic differential equation controls the evolution of the jet

```text
F=(f,f′,…,f^(n−1)).
```

If the minimal irreducible equation has nonzero separant along the solution, the equation can be locally solved for `f^(n)` and rewritten as a first-order companion system

```text
F′ = Φ(z,F).
```

The bounded-jet hypothesis gives Fatou boundary limits and keeps the trajectory away from the singular locus near almost every good boundary point. The analytic ODE existence theorem then gives a uniform continuation radius from nearby interior anchor points. This is the corrected core of the ADE + `H^∞` + natural-boundary theorem.

The correction is important. The naive version tried to apply Cauchy–Kowalewski directly to measurable Fatou boundary data. The repaired version anchors the initial value problem at an interior point and uses a uniform existence radius. In the story of the whole corpus, this is the differential analogue of the algebraic implicit-function theorem: a finite equation makes continuation possible unless the boundary data become too wild.

---

## 2. The common enemy: infinite boundary information

The finite constraints lose because the objects carry boundary information that is too large, too dense, or too arithmetically irregular.

The documents exhibit three main kinds of “infinite boundary information.”

### 2.1 Natural boundary

The lacunary series `u₀` has the unit circle as a natural boundary by Ostrowski–Hadamard. It is not enough to know that `u₀` is transcendental. The proof uses the stronger fact that `u₀` cannot be analytically continued through any point of `|z|=1`.

The ADE criterion abstracts this: if a function with a bounded algebraic-differential jet had a natural boundary, then the finite ODE would force continuation across almost every good boundary point. Therefore a bounded-jet natural boundary function must be hypertranscendental.

The Böttcher connected case uses a related but not identical boundary obstruction. The Julia set is not called a natural boundary in exactly the same elementary way as the lacunary unit circle, but the proof shows that analytic continuation of `φ_c` through a Julia point would force a smooth real-analytic piece of the Julia set, and Eremenko–van Strien rigidity then forces an exceptional circle/interval Julia set. Thus nonexceptional connected Julia boundaries function as rigid natural boundaries for the inverse Böttcher coordinate.

### 2.2 Infinite dyadic monodromy

The disconnected Böttcher coordinate can be analytically continued around holes in the Cantor complement, but it does not come back to itself. The exact monodromy theorem identifies the scalar multipliers as all dyadic roots of unity.

This is stronger than saying “the monodromy is infinite.” It says that for every depth `n`, one can isolate a clopen cylinder of harmonic measure `2^{-n}`, and the period of `d log φ_c` around it is

```text
2πi / 2^n.
```

That produces multipliers of arbitrarily large order. A polynomial relation of fixed degree has no way to absorb these arbitrarily high one-coordinate rotations.

### 2.3 Noninteger branch-tail memory

The Hurwitz cards deal with a different kind of infinity. Near `a=-n`, the shifted Hurwitz functions have singular expansions

```text
F_k(-n+x) = x^{-s-k} + R_{n,k}(x).
```

The leading terms create a rational-normal direction. At quadratic degree, there is a visible collision:

```text
F₀F₂ - F₁²
```

has cancellation in its most singular leading term. A naive algebraic relation might hope to exploit that cancellation.

The `N=2` card shows the first obstruction: the next term contains a regular-part value of the shape

```text
R_{n,0}(0) = ζ(s) + η H_n^(s),
```

and the finite difference of this sequence contains `n^{-s}`, which cannot be a finite difference of a rational function when `s` is nonintegral.

The all-`N` card replaces the initial finite-difference shortcut with a stronger rational-tail independence lemma. It translates a hypothetical rational dependence among generalized harmonic sums into a rational generating function, then uses the fractional polylog expansion near `z=1` and the pole tower at `μ=2πim` to force every polynomial coefficient to vanish.

Thus the Hurwitz obstruction is not primarily topological monodromy around Cantor holes. It is arithmetic/analytic memory stored in branch-regular tails.

---

## 3. The Böttcher independence story

The Böttcher documents are the most developed part of the corpus. They prove a named inverse-Böttcher algebraic independence theorem for quadratic polynomials.

Let

```text
f_c(z)=z²+c,
```

and let `φ_c` be the inverse Böttcher coordinate normalized by

```text
φ_c(f_c(z)) = φ_c(z)²,
φ_c(z)/z → 1  as z→∞.
```

The main theorem assembled in `q62-bottcher-independence-n2-all-parameters.md` says:

> If `c₁ ≠ c₂` and `c₁,c₂ ∉ {0,-2}`, then `φ_{c₁}` and `φ_{c₂}` are algebraically independent over `C(z)`.

The exceptions are exactly the monomial and Chebyshev cases in the quadratic family.

### 3.1 Why finite Laurent checks cannot prove it

One important anti-theatre point is that finite Laurent expansions are non-identifying. A fixed truncation depth can be misleading because triangular correction terms in `φ_{c₁}-z` can cancel observed coefficients off the diagonal `c₁=c₂`.

So the proof must be global. It cannot be a coefficient computation. It must use the geometry of analytic continuation.

That is the first major connection to the other documents: throughout the corpus, finite computations are not trusted unless they are embedded in a global obstruction. The global obstruction may be capacity, monodromy, natural boundary, or branch-tail independence.

### 3.2 Connected/connected case: crossing plus rigidity

When `c∈M`, the filled Julia set `K_c` is connected and the inverse Böttcher coordinate is single-valued on the basin of infinity

```text
Ω_c = C \ K_c.
```

Suppose there were a nonzero algebraic relation

```text
P(z, φ_{c₁}(z), φ_{c₂}(z)) = 0.
```

The proof first establishes a crossing:

```text
J_{c₁} ∩ Ω_{c₂} ≠ ∅
```

after possibly swapping indices.

The capacity argument is crucial. If `J_{c₁} ⊂ K_{c₂}`, fullness gives `K_{c₁} ⊂ K_{c₂}`. Both filled Julia sets have logarithmic capacity `1`. A strict containment of connected full compacta of the same capacity is excluded by an energy-variation or strong-minimum-principle argument. Equality of filled Julia sets forces equality of the quadratic parameter, contradicting `c₁≠c₂`.

At a crossing point `z₀ ∈ J_{c₁} ∩ Ω_{c₂}`, the coordinate `φ_{c₂}` is analytic. Away from the locally discrete bad locus of the algebraic relation, the algebraic implicit function theorem would continue `φ_{c₁}` through `z₀`.

But this is impossible. If `φ_{c₁}` continued through a Julia point, then locally the Julia set would lie in a smooth real-analytic curve `|Φ|=1` at a noncritical point. Eremenko–van Strien rigidity says that a relatively open smooth piece of a Julia set forces the whole Julia set into a circle. In the quadratic family, that gives only `c=0` or `c=-2`, which are excluded.

So the connected proof is a clean instance of the continuation-machine principle:

```text
algebraic relation + crossing domain + generic point
⇒ forbidden continuation through Julia boundary.
```

### 3.3 Disconnected/disconnected case: exact Prüfer monodromy

When `c∉M`, the filled Julia set is a Cantor set and `φ_c` has nontrivial scalar monodromy on `Ω_c=C\K_c`.

The exact monodromy theorem identifies the period group of `d log φ_c` as

```text
2πi Z[1/2],
```

and the scalar monodromy group as

```text
μ_{2^∞}.
```

The proof is potential-theoretic. On the chosen branch near infinity,

```text
d log φ_c = ∫_K dz/(z-ζ) dμ_c(ζ),
```

where `μ_c` is the equilibrium measure. For a loop `γ`,

```text
∫_γ d log φ_c = 2πi ∫_K Ind(γ,ζ) dμ_c(ζ).
```

Because `K_c` is a full-shift Cantor set and `μ_c` is the fair Bernoulli measure, a loop around a depth-`n` clopen cylinder has period `2πi/2^n`. Conversely, every continuous integer-valued index function on the Cantor set depends on finitely many symbols, so every period is dyadic.

This exact result is the monodromy engine in the disconnected independence proof.

For distinct disconnected parameters `c₁,c₂`, one first separates the Cantor sets: `K_{c₁}` is not contained in `K_{c₂}`. If containment held, uniqueness of the equilibrium measure and full support would force equality of the filled Julia sets, hence equality of the parameter via the Laurent coefficient.

Choose a disk `D ⊂ Ω_{c₂}` meeting `K_{c₁}` in a small depth-`n` cylinder. A loop in `D\K_{c₁}` around that cylinder multiplies `φ_{c₁}` by `exp(2πi/2^n)` but fixes `φ_{c₂}` because the loop lies in `Ω_{c₂}`. Reachability from the infinity germ is supplied by the fact that zero-dimensional compact plane sets do not separate.

If an algebraic relation existed, analytic continuation around the powers of this loop would give

```text
P(z, exp(2πik/2^n) φ_{c₁}(z), φ_{c₂}(z)) = 0
```

for `k=0,…,2^n-1`. Taking `2^n` larger than the degree in the first Böttcher coordinate gives too many roots. The remaining relation would involve only `φ_{c₂}`, contradicting its known transcendence/hypertranscendence in the nonexceptional case.

The disconnected proof is thus not a natural-boundary proof. It is a finite-degree-versus-infinite-monodromy proof.

### 3.4 Mixed case

The mixed case combines the two mechanisms. If one parameter is connected and the other is disconnected, the disconnected coordinate supplies the high dyadic monodromy, while the connected coordinate is single-valued on the relevant basin region and is therefore fixed by the chosen loop.

The needed crossing/separation again uses capacity and support. The path-placement step uses the no-cut property of zero-dimensional sets inside a plane region.

The result is that all nonexceptional pairs are covered.

### 3.5 What the Böttcher story contributes to the synthesis

The Böttcher cluster contributes three structural lessons.

First, **capacity is a crossing detector**. It repeatedly prevents one Julia set or compactum from hiding completely inside another when both have capacity `1` unless they are actually the same object.

Second, **potential theory is monodromy arithmetic**. In the disconnected case, equilibrium measure does not just prove existence of monodromy; it computes the exact period group.

Third, **finite algebraic dependence cannot control independent continuation behavior**. If one coordinate has a forbidden boundary while another is analytic across it, algebraic dependence would continue the first. If one coordinate has arbitrarily high one-coordinate monodromy while another is fixed, algebraic dependence would impose an impossible degree bound.

---

## 4. The `u₀` story: turning a degeneration leak into a theorem

The `u₀` cards are best read as a companion to the Böttcher independence theorem.

The function

```text
u₀(z)=Σ_{n≥0} 2^{-(n+1)} z^{-(2^{n+1}-1)}
```

is the `c`-velocity of the inverse Böttcher family at the monomial fiber:

```text
u₀ = (∂_c φ_c)|_{c=0}.
```

In the variable `x=1/z`, this becomes

```text
U₀(x)=u₀(1/x)=Σ_{n≥0} 2^{-(n+1)} x^{2^{n+1}-1}.
```

The exponents have Hadamard gaps, and the coefficient radius is `1`, so the unit circle is a natural boundary for `U₀`; equivalently, `u₀` cannot be analytically continued through any point of `|z|=1`.

The all-parameter theorem says:

> For every `b∈C` with `b≠0,-2`, the functions `u₀(z)` and `φ_b(z)` are algebraically independent over `Qbar(b,z)`.

### 4.1 Connected parameters: basin crosses the unit circle

For `b∈M\{0,-2}`, the coordinate `φ_b` is single-valued on `Ω_b=C\K_b`. The proof needs a point on the natural boundary of `u₀` where `φ_b` is analytic, i.e. a point in

```text
Ω_b ∩ {|z|=1}.
```

The card proves this crossing by capacity. If the unit circle did not meet `Ω_b`, then the closed unit disk would lie in `K_b`. Because both `K_b` and the closed unit disk have capacity `1`, strict containment is impossible by an energy test using a continuum outside the disk. Hence `K_b` would have to be the closed unit disk. Complete invariance of the Julia set would then force `b=0`, excluded.

Thus `Ω_b` crosses the unit circle.

If a relation

```text
P(z,u₀(z),φ_b(z))=0
```

existed and involved `u₀`, then over the field generated by `z` and `φ_b`, the function `u₀` would be algebraic. Avoid the discrete leading-coefficient and discriminant bad loci, choose a crossing point on the unit circle, and continue `u₀` through that point using the algebraic implicit function theorem. This contradicts the natural boundary.

If the relation does not involve `u₀`, then it makes `φ_b` algebraic over `Qbar(b,z)`, contradicting the known nonexceptional Böttcher transcendence classification.

### 4.2 Disconnected parameters: Green-crossing replaces basin-crossing

For `b∉M`, the coordinate `φ_b` is not single-valued on all of `Ω_b`. It is single-valued on the larger-than-critical Green domain

```text
Δ_b = { z : G_b(z) > G_b(0) }.
```

So the needed crossing becomes

```text
{|z|=1} ∩ Δ_b ≠ ∅.
```

The disconnected card proves this by the Green-crossing lemma:

> For every `b∉M`, `b≠0`, there exists `z₀` on the unit circle with `G_b(z₀)>G_b(0)`.

The proof splits into two cases.

If `K_b` meets the open unit disk, Riesz–Jensen gives

```text
mean_{|z|=1} G_b - G_b(0)
= ∫_{|w|<1} log(1/|w|) dμ_b(w) > 0,
```

so some boundary value exceeds `G_b(0)`.

If `K_b` misses the open unit disk, then `G_b` is harmonic on the disk. If `K_b` touches the unit circle, one boundary value is `0<G_b(0)`, so another must be above the mean. If `K_b` misses the closed disk, the strong maximum principle again gives a strict boundary maximum.

Once this crossing is established, the same algebraic-continuation contradiction works inside `Δ_b`.

### 4.3 What the `u₀` story contributes

The `u₀` story contributes a new kind of bridge.

The Böttcher pair theorem concerns two inverse Böttcher coordinates. The `u₀` theorem concerns a tangent object at the exceptional monomial fiber and a genuine nonexceptional Böttcher coordinate. It shows that the degeneration at `c=0` does not produce an algebraic escape route. The tangent leak is itself independent.

This fits the global story because `u₀` is a pure natural-boundary object, while `φ_b` supplies a crossing analytic domain. Finite algebraic dependence would turn that crossing into forbidden continuation.

---

## 5. The Hurwitz story: branch tails defeat quadratic algebraic repair

The Hurwitz cards look different at first. They do not involve Julia sets, Böttcher coordinates, or capacity. But they share the same obstruction pattern: a finite algebraic relation tries to compress singular behavior into rational data; the singular tails refuse to be compressed.

Fix `Re(s)>1`, `s∉Z`, and set

```text
F_k(a)=ζ(s+k,a).
```

The all-`N` theorem says:

> For every finite ladder `{F_k}_{0≤k≤N}`, there is no nonzero `C(a)`-polynomial relation of total degree at most two.

Using

```text
∂_a^k ζ(s,a)=(-1)^k (s)_k ζ(s+k,a),
```

this excludes algebraic ODEs for `ζ(s,a)` of order at most `N` and polynomial degree at most two in the jet variables.

This is not full hypertranscendence. It is a uniform quadratic obstruction.

### 5.1 The `N=2` density shadow

For `N=2`, the most dangerous quadratic collision is

```text
F₀F₂ - F₁².
```

Near `a=-n`, with `x=a+n`, one has

```text
F_k(-n+x)=x^{-s-k}+R_{n,k}(x).
```

The leading term of `F₀F₂` is

```text
x^{-s} x^{-s-2} = x^{-2s-2},
```

and the leading term of `F₁²` is

```text
x^{-s-1} x^{-s-1} = x^{-2s-2}.
```

So the leading rational-normal term cancels in `F₀F₂-F₁²`. This is exactly where a quadratic algebraic relation might hide.

The card shows that the next term exposes the hidden tail:

```text
F₀F₂-F₁² = x^{-s-2} R_{n,0}(0) + O(x^{-s-1}),
```

and

```text
R_{n,0}(0)=ζ(s)+η H_n^(s).
```

If a rational coefficient `q(a)` repaired the collision, then `R_{n,0}(0)` would be rationally interpolable in `n`. But its finite difference is `η n^{-s}`, and a finite difference of a rational function has an asymptotic expansion in integral powers of `n`. Since `s` is not an integer, this is impossible.

Thus the first nonlinear collision is not repairable.

### 5.2 The all-`N` row descent

The all-`N` theorem generalizes this by proving a rational-tail independence lemma.

Suppose rational functions `r_j(n)` and `R(n)` satisfied

```text
Σ_{j=0}^M r_j(n) H_n^(s+j) = R(n)
```

for all sufficiently large integers `n`. The lemma proves every `r_j` must vanish.

The proof converts the sequence identity into a generating-function identity involving

```text
Li_{s+j}(z)/(1-z).
```

Putting `z=e^{-μ}`, the fractional polylogarithm has a noninteger branch expansion near `μ=0`:

```text
Li_α(e^{-μ}) = Γ(1-α) μ^{α-1} + integral-power terms.
```

The branch part cannot occur in a rational function of `z`. To prove injectivity, the proof uses the pole tower of

```text
h(μ)=1/(1-e^{-μ})
```

at nonzero `μ_m=2πim`. The highest derivative order gives coefficients involving an ordinary polynomial in `μ_m` with infinitely many roots, forcing its coefficients to vanish. Descending on degree kills all rational-tail coefficients.

Then the quadratic row descent proceeds by weights. The `T²` coefficient kills the rational-normal quadratic sums. The `T¹` coefficient, read column by column from the highest shift downward, invokes rational-tail independence to kill the remaining quadratic and linear coefficients. The constant term then vanishes.

### 5.3 What the Hurwitz story contributes

The Hurwitz cards contribute a third obstruction template.

In Böttcher connected cases, algebraic relations fail because they would continue through a geometric boundary.

In Böttcher disconnected cases, algebraic relations fail because they cannot absorb one-coordinate dyadic monodromy.

In Hurwitz shift ladders, algebraic relations fail because they cannot rationally absorb noninteger branch-tail sequences.

This suggests the broader principle:

> A finite algebraic relation can only hide singularities if the singular data reduce to finite algebraic, finite monodromy, or rationally interpolable information. The Hurwitz tails are none of these.

---

## 6. The ADE bounded-jet theorem as the abstract capstone

The ADE card is the most abstract document in the set. It does not prove algebraic independence of a pair of named Böttcher coordinates or a quadratic relation for a named shift ladder. Instead, it gives a criterion:

> Let `f` be holomorphic on the unit disk and satisfy a minimal irreducible differential annihilator
> 
> ```text
> P(z,f,…,f^(n))=0
> ```
> 
> over `C(z)`. If
> 
> ```text
> f,f′,…,f^(n) ∈ H^∞(D),
> ```
> 
> then the unit circle is not a natural boundary of `f`.

Equivalently:

> If `f` has a natural boundary and bounded order-`n` jet, then `f` is hypertranscendental.

### 6.1 The false start and the corrected proof

The document explicitly records a methodological correction.

The first Fatou + Cauchy–Kowalewski proof sketch was too quick. Fatou gives boundary limits almost everywhere, but Cauchy–Kowalewski requires analytic initial data, not merely measurable point limits.

The corrected proof uses the first-order companion system.

Let

```text
F=(f,f′,…,f^(n−1)).
```

Where the separant

```text
S = ∂P/∂y^(n)
```

is nonzero, solve the equation locally for

```text
f^(n)=R(z,f,…,f^(n−1)).
```

Then

```text
F′=Φ(z,F),
```

where `Φ` is analytic away from the separant-zero locus.

The proof needs `S∘f` not to vanish identically. This is where minimal irreducibility matters. If `S∘f≡0`, then `P` and `S` share `f^(n)` as a common root. Since `P` is irreducible, the resultant in `y^(n)` gives a lower-order differential polynomial vanishing on `f`, contradicting minimality.

Now, because the order-`n` jet is bounded, Fatou gives radial limits of the lower jet almost everywhere, and the separant expression belongs to a bounded/Nevanlinna class. The nonzero separant has nonzero radial limit almost everywhere. At a good boundary point, the jet approaches a compact subset away from the singular locus of `Φ`.

The analytic ODE existence theorem supplies a uniform radius of existence for initial data near that compact set. Choose an interior point sufficiently close to the boundary. The IVP solution through that actual interior jet equals `F` inside the disk by uniqueness and extends across the boundary because the existence disk crosses it.

Thus `f` continues past at least one boundary point, contradicting natural boundary.

### 6.2 Why the order-`n` bounded jet is natural

The sharpened theorem requires only

```text
f,f′,…,f^(n) ∈ H^∞(D),
```

not all derivatives.

The lower jet `f,…,f^(n−1)` is needed for Fatou boundary data and compactness in the companion system. The derivative `f^(n)` is needed because the separant `S` is a polynomial in `f,…,f^(n)`; controlling its boundary behavior uses boundedness/Nevanlinna-class arguments.

The document explicitly leaves open whether `f∈H^∞` alone could suffice. It conjectures that this is probably false: algebraic branch points can keep `f` bounded while blowing up derivatives. A DA solution with finite-value branch points accumulating densely at the boundary would be bounded with a natural boundary but would evade the bounded-jet theorem.

This frontier is important for the whole synthesis. Many natural-boundary objects in the other documents are bounded or controlled at the function level but not necessarily at the derivative-jet level. The ADE theorem is therefore not a black-box proof of the Böttcher, `u₀`, or Hurwitz results. It is a conceptual capstone that explains why finite differential constraints are incompatible with sufficiently tame natural boundaries.

### 6.3 How the ADE theorem connects to the other clusters

The connection is not direct implication. It is structural analogy.

- In the `u₀` theorem, the lacunary natural boundary is used directly against algebraic dependence with `φ_b`. The ADE theorem says that if a natural-boundary object also satisfied a bounded-jet algebraic differential equation, it would be forced across the boundary. Thus the same “finite equation implies continuation” logic appears in differential form.
- In the connected Böttcher theorem, the Julia boundary blocks analytic continuation. The ADE theorem abstracts a setting where bounded differential-algebraic structure would force such continuation.
- In the disconnected Böttcher theorem, the problem is not absence of continuation but too much multivalued continuation. The ADE theorem does not cover this, but the same finite-control theme is present.
- In the Hurwitz theorem, local singular expansions and branch tails obstruct low-degree algebraic differential relations. The ADE theorem suggests that full hypertranscendence may require showing that any hypothetical ADE would create continuation or boundary regularity incompatible with the actual singular-tail structure.

---

## 7. The hidden architecture: three proof templates

Across the documents, the same proof architecture appears in three templates.

### Template I — Crossing plus algebraic implicit continuation

Input:

1. A function `A` has a forbidden boundary `B`.
2. A function `C` is analytic on a domain crossing `B`.
3. A supposed algebraic relation makes `A` algebraic over `z` and `C`.
4. A generic crossing point avoids leading-coefficient and discriminant bad loci.

Conclusion:

```text
A continues through B, contradiction.
```

Used in:

- connected Böttcher independence;
- connected `u₀ ⊥ φ_b`;
- disconnected `u₀ ⊥ φ_b` after Green-crossing;
- connected/mixed pieces where one coordinate is analytic across the other’s bad boundary.

### Template II — One-coordinate high monodromy

Input:

1. A loop fixes all but one coordinate.
2. The remaining coordinate is multiplied by roots of unity of arbitrarily high order.
3. A supposed algebraic relation has fixed finite degree in that coordinate.

Conclusion:

```text
too many roots for a fixed-degree polynomial, contradiction.
```

Used in:

- disconnected/disconnected Böttcher independence;
- mixed connected/disconnected Böttcher independence.

### Template III — Singular-row descent and tail independence

Input:

1. A supposed polynomial relation is expanded near infinitely many singular points.
2. Leading exponents split into weights.
3. Apparent collisions leave regular branch-tail sequences.
4. Those tail sequences are independent over rational functions.

Conclusion:

```text
all coefficients vanish by descending through weights/columns.
```

Used in:

- Hurwitz `N=2` density shadow;
- Hurwitz all-`N` quadratic tail independence.

### Template IV — Bounded companion-system continuation

Input:

1. A function satisfies a minimal irreducible ADE.
2. Its order-`n` jet is bounded on the disk.
3. The separant is nonzero generically.
4. Fatou plus boundedness gives good boundary approach regions away from the ODE singular locus.

Conclusion:

```text
analytic ODE continuation crosses the boundary, contradiction to natural boundary.
```

Used in:

- ADE + `H^∞` + natural boundary ⇒ hypertranscendence.

Template IV is the differential version of Template I. Template II is the multivalued version. Template III is the singular-expansion version.

---

## 8. Analytical gaps filled by the synthesis

This section states connective claims that are not always explicit in the individual cards but help turn them into one story.

### Gap 1 — Why capacity appears in several unrelated-looking places

Capacity appears in the Böttcher pair theorem and in the `u₀` crossing theorem because it is the invariant that prevents compact filled Julia sets of monic polynomials from being nested too freely.

All quadratic filled Julia sets have capacity `1`. The closed unit disk also has capacity `1`. Therefore, if a connected full compactum of this type strictly contains another connected full compactum of the same capacity, something must be wrong. The energy-variation argument detects the strict containment by moving a small amount of equilibrium mass into the extra continuum and lowering energy, which raises capacity.

This crossing is not a technical convenience. It is the geometric reason that one analytic domain must meet another object’s boundary.

### Gap 2 — Why exact monodromy is stronger than transcendence

Knowing that a single Böttcher coordinate is transcendental does not by itself prove pairwise algebraic independence. A relation between two transcendental functions could still exist.

The disconnected proof needs a stronger invariant: loops that move one coordinate through arbitrarily many distinct values while fixing the other. Exact Prüfer monodromy provides this. The algebraic relation cannot have enough degree to absorb all those rotated branches.

Thus exact monodromy is a pairwise independence tool, not merely a single-function transcendence tool.

### Gap 3 — Why the `u₀` theorem is not just a corollary of Böttcher independence

The function `u₀` is not itself a nonexceptional Böttcher coordinate. It is a derivative at the exceptional monomial parameter `c=0`. Nguyen Q6.2 for two nonexceptional coordinates does not directly cover it.

The `u₀` theorem converts the obstruction caused by trying to degenerate `c₁→0` into an independent theorem: even the tangent object at the exceptional fiber remains algebraically independent from every nonexceptional coordinate.

This matters because degeneration arguments often fail precisely at exceptional fibers. The theorem says the first-order leak is still too wild to be algebraically controlled.

### Gap 4 — Why the Hurwitz theorem belongs in the same story

The Hurwitz theorem has no Julia set and no Böttcher coordinate. But it has the same formal shape: finite algebraic dependence would impose finite control on singular behavior.

At each `a=-n`, the local branch singularity has a leading direction plus a regular tail. Quadratic relations can cancel leading terms, just as algebraic relations can sometimes cancel principal parts. But the tails vary with `n` through generalized harmonic sums. The rational-tail lemma says these tails cannot be rationally interpolated.

So the Hurwitz theorem is the branch-tail version of the same finite-control obstruction.

### Gap 5 — Why the ADE theorem is not a universal black box

The ADE theorem only applies under a bounded order-`n` jet hypothesis. Many functions in the corpus have natural boundaries or singular boundaries but do not obviously satisfy such bounded-jet conditions. For instance, lacunary series can be bounded while derivatives blow up; Böttcher coordinates near fractal Julia boundaries can have severe derivative behavior; Hurwitz zeta has explicit singularities.

Therefore the ADE theorem does not subsume the rest. Instead, it explains one regime where the same philosophy becomes a general theorem.

### Gap 6 — Why “finite covers cannot kill it” matters

The Prüfer group is divisible. This means finite-index restrictions cannot remove the dyadic monodromy. In practical terms, no finite algebraic cover can trivialize the disconnected Böttcher continuation behavior.

That is stronger than saying no polynomial relation exists in one coordinate. It says the obstruction is inherently infinite-level. Any proof strategy that tries to pass to a finite branched cover to make the coordinate single-valued is structurally doomed.

### Gap 7 — Why the bad loci do not ruin the continuation arguments

Several proofs require choosing crossing points away from a locally discrete bad set: coefficient poles, leading coefficient zeros, discriminant zeros, or multiple-root loci. This works because the relevant crossing sets are not discrete. They contain arcs, relatively open Julia-boundary pieces, or enough boundary points to avoid a locally finite exceptional set.

The generic-point step is the quiet hinge of the algebraic-implicit-function arguments.

### Gap 8 — Why the separant issue in the ADE theorem is serious

In a nonlinear differential equation, solving for the highest derivative can fail on singular solutions. The ADE card fixes this by requiring the minimal annihilator to be irreducible and by using a resultant argument to rule out identically vanishing separant along `f`.

This mirrors the algebraic independence proofs, where discriminant bad loci must be avoided. In both cases, the finite relation gives continuation only away from singular algebraic degeneracies. The proof must show those degeneracies cannot occupy the whole relevant set.

---

## 9. A single narrative version

Here is the story as one continuous arc.

Start with the inverse Böttcher coordinate. Near infinity it is a well-behaved local conjugacy, but globally it remembers the Julia set. If the Julia set is connected, the coordinate is single-valued in the basin of infinity but cannot pass through a nonexceptional Julia boundary. If the Julia set is disconnected, the coordinate can be continued around the Cantor complement, but it accumulates exact dyadic monodromy measured by equilibrium measure on symbolic cylinders.

Now ask Nguyen’s inverse-coordinate question for two parameters. A finite algebraic relation would tie the two coordinates together. If both Julia sets are connected, capacity forces one Julia boundary to cross the other coordinate’s basin. At that crossing, the relation would continue one coordinate through its forbidden boundary. Rigidity forbids that. If one or both Julia sets are disconnected, Cantor-cylinder loops move one coordinate by arbitrarily high dyadic roots of unity while fixing the other. A finite-degree relation cannot survive that. Thus distinct nonexceptional quadratic inverse Böttcher coordinates are algebraically independent.

Next, examine the exceptional monomial fiber `c=0`. The first parameter derivative of the inverse Böttcher coordinate is a lacunary series `u₀`. It has a hard natural boundary at the unit circle. This object could have been a leak in the Böttcher independence program: perhaps degenerating one coordinate to the exceptional fiber creates an algebraic relation between the tangent and the remaining coordinate. But the same continuation principle blocks that. For connected `b`, capacity forces the Böttcher basin to cross the unit circle. For disconnected `b`, the Green-crossing lemma forces the single-valued domain `Δ_b` to cross the unit circle. At a generic crossing point, a finite algebraic relation would continue `u₀` through its natural boundary. So the tangent leak is independent from every nonexceptional `φ_b`.

Then move to Hurwitz zeta. The domain geometry changes, but the obstruction principle survives. The shift ladder `ζ(s+k,a)` has singular expansions at negative integers. Quadratic algebraic relations can attempt to cancel leading singular directions; in the minimal `N=2` case, `F₀F₂-F₁²` is the visible collision. But the regular parts contain generalized harmonic sums with noninteger exponent memory. Rational functions cannot interpolate those tails. The all-`N` theorem proves this by translating rational-tail dependence into fractional polylogarithms and killing it with branch expansions and pole towers. Thus the Hurwitz ladder defeats finite quadratic algebraic control not by Julia geometry or Cantor monodromy, but by arithmetic branch-tail independence.

Finally, abstract the continuation principle into differential algebra. If a function on the disk satisfied a finite algebraic differential equation and had a bounded order-`n` jet, then the equation could be converted into a first-order companion system near almost every good boundary point. Boundedness and Fatou limits give enough compactness to anchor an interior IVP and continue across the unit circle. Therefore a bounded-jet natural boundary function cannot be differentially algebraic. It must be hypertranscendental.

The four clusters are therefore not isolated. They are four manifestations of the same slogan:

> Finite algebraic structure wants finite continuation control. The objects here carry infinite boundary data. The mismatch forces independence or hypertranscendence.

---

## 10. Conjectural bridges that may be false

This section intentionally goes beyond the proved cards. Each item is a possible research bridge. Some may be false.

### Conjecture 1 — Universal finite-continuation obstruction principle

**Statement.** There is a general theorem behind these cards: if a tuple of analytic germs has continuation data whose monodromy/boundary/tail invariant is not representable by a finite algebraic correspondence over `C(z)`, then the tuple is algebraically independent over `C(z)` modulo obvious exceptional symmetries.

**Why it fits.**

- Connected Böttcher: finite correspondence would continue through a forbidden boundary.
- Disconnected Böttcher: finite correspondence cannot absorb Prüfer monodromy.
- `u₀`: finite correspondence would cross a lacunary natural boundary.
- Hurwitz: finite quadratic correspondence cannot absorb noninteger tail memory.

**Why it may be false.**

“Continuation data not representable by a finite algebraic correspondence” is not yet a precise invariant. There may be analytic functions with wild continuation behavior but accidental algebraic relations due to hidden symmetries. The conjecture needs a formal category of germs, correspondences, and continuation groupoids before it can even be tested.

### Conjecture 2 — Higher-degree Hurwitz shift-ladder independence

**Statement.** For `Re(s)>1`, `s∉Z`, every finite Hurwitz shift ladder `{ζ(s+k,a)}_{0≤k≤N}` is algebraically independent over `C(a)`, not just free of relations of total degree at most two.

**Why it fits.**

The all-`N` quadratic theorem suggests that rational coefficients cannot hide branch-regular tails. Higher-degree relations would produce more complicated collisions, but the same generalized harmonic tail sequences and fractional-polylog pole towers may still force all coefficients to vanish.

**Why it may be false.**

Higher-degree products produce multiple zeta-like convolution tails, not only linear generalized harmonic sums. New identities could appear among these higher convolution tails. The quadratic row descent may not generalize without a much stronger algebra of tail independence.

### Conjecture 3 — Full hypertranscendence of Hurwitz in the weld model

**Statement.** For `Re(s)>1`, `s∉Z`, the function `a↦ζ(s,a)` is hypertranscendental over `C(a)` by a strengthened version of the tail-independence method.

**Why it fits.**

The derivative ladder is exactly the shift ladder up to Pochhammer factors:

```text
∂_a^k ζ(s,a)=(-1)^k(s)_k ζ(s+k,a).
```

So algebraic differential relations become algebraic relations among finite shift ladders. The quadratic all-`N` theorem is the first uniform nonlinear gate.

**Why it may be false or incomplete.**

The cards only handle degree `≤2`. Full hypertranscendence requires all polynomial degrees and all orders. The combinatorics of branch-tail products may become far more complicated, and standard functional identities for zeta/polylogarithms may introduce unexpected dependencies.

### Conjecture 4 — Higher-degree Böttcher Q6.2 analogue

**Statement.** For polynomial families beyond the quadratic case, inverse Böttcher coordinates attached to distinct nonexceptional parameters are algebraically independent except for explicitly classified shared-iterate, monomial, Chebyshev, or symmetry cases.

**Why it fits.**

The quadratic proof uses ingredients with higher-degree analogues:

- capacity of monic polynomial filled Julia sets;
- exterior Böttcher maps;
- rigidity of smooth Julia pieces;
- disconnected symbolic dynamics and harmonic measure on cylinders.

For degree `d`, disconnected monodromy should plausibly involve `d`-adic denominators rather than dyadic denominators.

**Why it may be false.**

Higher-degree parameter spaces have more critical points, more symmetries, and more ways for filled Julia sets or Böttcher coordinates to share structure. The exact two-parameter separation argument may fail without a one-critical-point normalization.

### Conjecture 5 — Exact `d`-adic Prüfer monodromy for disconnected degree-`d` Böttcher coordinates

**Statement.** For a monic degree-`d` polynomial with disconnected filled Julia set and full-shift dynamics on the Julia set, the scalar monodromy image of the inverse Böttcher coordinate is the Prüfer `d`-group, with period group

```text
2πi Z[1/d].
```

**Why it fits.**

The quadratic proof uses fair Bernoulli mass `2^{-n}` on depth-`n` cylinders. For a full `d`-shift, cylinder masses are `d^{-n}`.

**Why it may be false.**

Not every disconnected degree-`d` Julia set is a clean full shift with equal symbolic cylinder masses in the required sense, especially with multiple critical escape rates. The monodromy image may depend on the distribution of harmonic measure among nonuniform cylinders, producing a subgroup more complicated than `Z[1/d]`.

### Conjecture 6 — The `u₀` theorem is the first member of a velocity-independence tower

**Statement.** Let

```text
u_m(z) = (∂_c^m φ_c(z))|_{c=0}
```

or suitable normalized higher parameter velocities at the monomial fiber. Then for every nonexceptional `b`, the collection

```text
u_0, u_1, …, u_M, φ_b
```

is algebraically independent over `Qbar(b,z)`, apart from any formal relations forced by the differentiated Böttcher equation.

**Why it fits.**

The first velocity `u₀` is lacunary and has a natural boundary. Higher velocities are expected to inherit lacunarity or even denser gap structures from iterated differentiation of the Böttcher functional equation.

**Why it may be false.**

Higher parameter derivatives may satisfy algebraic or differential recurrences inherited from the family equation. They may not be independent of `u₀`; they could be polynomially generated by lower velocities plus rational/Böttcher terms.

### Conjecture 7 — Bounded-jet ADE theorem has a sharp converse frontier

**Statement.** The order-`n` bounded-jet hypothesis in the ADE theorem is close to optimal. In particular, there should exist a bounded differentially algebraic function on the disk with a natural boundary if derivative boundedness is removed.

**Why it fits.**

Finite-value algebraic branch points can keep `f` bounded while making `f′` blow up. A solution with such branch points accumulating densely on the boundary would evade the bounded-jet theorem.

**Why it may be false.**

Constructing a genuine differentially algebraic function with a dense natural boundary of finite-value branch points may be impossible under deeper constraints on algebraic ODEs. The conjectured quasi-Painlevé mechanism is plausible but not yet an example.

### Conjecture 8 — The ADE theorem can be localized to arbitrary analytic Jordan domains

**Statement.** The bounded-jet ADE criterion should hold not only for the unit disk but for any sufficiently regular simply connected domain, after transporting the Hardy/Fatou boundary theory appropriately.

**Why it fits.**

The proof uses Fatou limits, boundedness of the jet, and local analytic ODE continuation. These are not intrinsically tied to the circle except through boundary limit theory.

**Why it may be false or require qualification.**

For rough boundaries, Fatou theory and nontangential approach regions can fail or require harmonic measure formulations. Even for Jordan domains, derivative transformations under conformal maps can distort bounded-jet hypotheses.

### Conjecture 9 — Hurwitz tail independence is an additive analogue of Prüfer monodromy

**Statement.** The rational-tail obstruction in the Hurwitz cards is the additive/branch analogue of the dyadic Prüfer monodromy obstruction in the disconnected Böttcher cards.

**Why it fits.**

Both create infinitely many incompatible finite constraints indexed by a discrete depth/level parameter:

- Böttcher: depth-`n` cylinders give periods `2πi/2^n`.
- Hurwitz: singularities at `a=-n` give tails involving `H_n^(s+j)` and noninteger powers `n^{-s-j}`.

Both defeat finite algebraic control by producing infinitely many independent levels.

**Why it may be false.**

The Böttcher obstruction is genuine topological monodromy. The Hurwitz obstruction is asymptotic and arithmetic. A formal equivalence may be misleading unless both are placed in a common groupoid or resurgence framework.

### Conjecture 10 — Capacity-crossing is the geometric shadow of algebraic independence

**Statement.** In polynomial dynamics, many algebraic independence results for Böttcher-type functions reduce to a capacity-crossing lemma plus a local continuation obstruction.

**Why it fits.**

The connected Q6.2 proof and the connected `u₀` proof both rely on capacity to force an analytic domain to cross a forbidden boundary.

**Why it may be false.**

Some algebraic independence results may arise from arithmetic specialization, unlikely intersections, canonical heights, or model-theoretic dynamics rather than analytic crossing. Capacity-crossing may be powerful only for one-variable function-field relations.

### Conjecture 11 — Natural boundary and exact monodromy are two phases of the same obstruction

**Statement.** Connected Julia sets produce natural-boundary-type obstruction for `φ_c`, while disconnected Julia sets produce exact monodromy obstruction; these are two phases of a single boundary groupoid that changes at the Mandelbrot boundary.

**Why it fits.**

The all-parameter Böttcher theorem splits by connectedness. The proof mechanism changes, but the conclusion is the same: finite algebraic dependence fails.

**Why it may be false.**

The connected obstruction uses rigidity of smooth Julia pieces, while the disconnected obstruction uses Cantor cylinder monodromy. There may be no continuous groupoid deformation connecting the two mechanisms across the Mandelbrot boundary.

### Conjecture 12 — The “anti-theatre” principle can be formalized

**Statement.** The cards implicitly use a methodological principle: finite truncations cannot prove global algebraic independence unless paired with a global obstruction invariant. This principle could be formalized as a checklist for future theorem cards.

**Why it fits.**

Several cards explicitly reject finite computation as nonidentifying or insufficient. The successful proofs all introduce global invariants: capacity, monodromy, natural boundary, Fatou/ODE continuation, or fractional-polylog branch structure.

**Why it may be false.**

There are legitimate finite computation proofs in algebraic geometry and differential algebra, for example via resultants, Gröbner bases, or effective bounds. The principle should not ban finite computation; it should only ban unsupported finite-jet extrapolation.

---

## 11. Possible failure points and audit checklist

A synthesis document should not hide the weak points. The following are the places where the whole program most needs careful auditing.

### 11.1 Source novelty audits

Several cards claim bridge-grade novelty rather than deep-new-mathematics novelty. The ingredients are classical: potential theory, Böttcher coordinates, Eremenko–van Strien rigidity, Fatou theory, analytic ODE existence, fractional polylog expansions. The novelty claim is the assembled cross-corpus theorem.

A source kill would be a prior theorem that directly implies:

- Nguyen Q6.2 for inverse Böttcher coordinates in the quadratic all-parameter nonexceptional case;
- exact Prüfer monodromy of disconnected quadratic Böttcher coordinates as used here;
- `u₀ ⊥ φ_b` for all nonexceptional `b`;
- the bounded-jet ADE natural-boundary criterion;
- all-`N` Hurwitz quadratic shift-ladder independence.

The synthesis should be revised if any such source is found.

### 11.2 Exact monodromy loop construction

The exact monodromy theorem rests on the ability to realize index functions that isolate clopen Cantor cylinders by loops in the complement. This is plausible and recorded as proved, but it is a key topological construction. In a publication version, it deserves a fully explicit planar lemma.

### 11.3 Path reachability in complements

The disconnected and mixed Böttcher proofs use the fact that zero-dimensional compact plane sets do not separate plane regions. This is a classical Mazurkiewicz-type input. The exact hypotheses should be stated carefully, especially in the mixed case where a zero-dimensional set is removed from a connected basin.

### 11.4 Smooth-piece rigidity scope

The connected Böttcher proof relies on Eremenko–van Strien in the form: if a relatively open subset of a Julia set lies in a smooth curve, then the whole Julia set lies in a circle. The card records that this applies without local connectivity assumptions. A publication version should quote the exact theorem and verify the hypotheses for all connected nonexceptional quadratic Julia sets.

### 11.5 ADE separant and boundary-zero arguments

The ADE theorem depends on three delicate steps:

1. minimal irreducible annihilator implies separant not identically zero along `f`;
2. the separant expression has nonzero boundary limit almost everywhere;
3. the analytic ODE existence radius can be made uniform near a good boundary approach.

The card gives plausible and largely standard arguments. A final version should specify the exact boundary uniqueness theorem used for the separant and the exact complex ODE theorem used for the uniform radius.

### 11.6 Hurwitz higher-degree frontier

The all-`N` Hurwitz theorem is only quadratic. It is tempting to overstate it as near-hypertranscendence, but the cards correctly avoid that. Higher-degree products may require a much larger tail algebra.

### 11.7 The `u₀` derivative-boundedness issue

`u₀` is bounded as a lacunary series with summable coefficients in the exterior variable, but its derivatives need not satisfy the bounded-jet hypotheses of the ADE theorem. Therefore one should not cite the ADE theorem as proving hypertranscendence of `u₀` without additional derivative estimates or a different argument.

---

## 12. Roadmap suggested by the synthesis

The documents suggest a research roadmap.

### 12.1 Extract three standalone papers

1. **Quadratic inverse Böttcher independence.**
   
   Core theorem: all nonexceptional quadratic parameters `c₁≠c₂` give algebraically independent `φ_{c₁},φ_{c₂}`.
   
   Main ingredients: capacity crossing, Eremenko–van Strien rigidity, exact Prüfer monodromy, zero-dimensional path reachability.

2. **The monomial velocity `u₀` and Böttcher coordinates.**
   
   Core theorem: `u₀` is algebraically independent from every nonexceptional `φ_b`.
   
   Main ingredients: Ostrowski–Hadamard natural boundary, capacity crossing, Green-crossing lemma, algebraic IFT.

3. **Quadratic Hurwitz shift-ladder independence.**
   
   Core theorem: every finite ladder `{ζ(s+k,a)}` is free of `C(a)`-polynomial relations of total degree `≤2`.
   
   Main ingredients: local expansions at `a=-n`, rational-tail independence, fractional polylog branch expansion, pole-tower descent.

The ADE bounded-jet theorem could be a fourth short note or an abstract appendix tying the continuation philosophy together.

### 12.2 Formalize reusable lemmas

The cards repeatedly use a small number of reusable lemmas. Formalizing or at least isolating them would strengthen the corpus.

- Algebraic IFT continuation lemma for a germ algebraic over analytic functions along a path avoiding discriminant and poles.
- Capacity strict-containment lemma for connected full compacta of equal capacity.
- Zero-dimensional no-cut path lemma for plane regions.
- One-coordinate monodromy degree obstruction.
- Companion-system continuation lemma for bounded jets and nonzero separant.
- Rational-tail independence lemma for generalized harmonic sums.

### 12.3 Find or disprove the quasi-Painlevé bounded natural-boundary example

The ADE card’s frontier asks whether `f∈H^∞` alone can replace bounded order-`n` jet. The conjectured countermechanism is a DA solution with finite-value algebraic branch points accumulating at the boundary.

A concrete example or impossibility theorem would clarify the exact sharpness of the ADE criterion.

### 12.4 Push Hurwitz beyond quadratic degree

The natural next Hurwitz target is cubic degree for finite ladders. The point is not merely to prove one more case but to identify the correct algebra of higher tail products.

A likely test case is the first nontrivial cubic collision among

```text
F_i F_j F_k
```

with equal total shift weight. One should determine whether the regular tails reduce to known independent families or whether new relations appear.

### 12.5 Extend exact monodromy beyond quadratic shift locus

The exact dyadic monodromy theorem is a model. The next step is to determine the precise monodromy group for disconnected Böttcher coordinates in higher-degree or non-full-shift settings. The result may be `Z[1/d]`, or it may be a harmonic-measure value group depending on the symbolic dynamics.

---

## 13. A compressed theorem web

The following table compresses the proof relationships.

| Cluster | Object | Finite constraint attacked | Infinite obstruction | Proof template |
|---|---|---:|---|---|
| ADE | bounded-jet holomorphic `f` | algebraic differential equation | natural boundary + Fatou/ODE contradiction | companion-system continuation |
| Böttcher connected | `φ_{c₁}, φ_{c₂}` | algebraic relation | forbidden Julia-boundary continuation | crossing + algebraic IFT |
| Böttcher disconnected | `φ_{c₁}, φ_{c₂}` | algebraic relation | exact Prüfer `2`-monodromy | one-coordinate monodromy |
| Mixed Böttcher | connected/disconnected pair | algebraic relation | dyadic monodromy with other coordinate fixed | one-coordinate monodromy + path placement |
| `u₀` connected | `u₀, φ_b` | algebraic relation | lacunary natural boundary | crossing + algebraic IFT |
| `u₀` disconnected | `u₀, φ_b` | algebraic relation | lacunary natural boundary + Green crossing | Green-crossing + algebraic IFT |
| Hurwitz `N=2` | `ζ(s),ζ(s+1),ζ(s+2)` ladder | quadratic relation | noninteger harmonic tail | singular expansion descent |
| Hurwitz all-`N` | finite shift ladder | quadratic relation | rational-tail independence | polylog branch/pole tower |

---

## 14. Final synthesis

The uploaded documents form a coherent research program around a single principle:

> Finite algebraic structures are continuation devices. They fail when the analytic object carries boundary data that are too infinite to be finitely continued, finitely branched, or rationally interpolated.

The Böttcher theorems show this in complex dynamics. Connected Julia sets block continuation by rigidity; disconnected Julia sets create exact dyadic monodromy. The `u₀` theorem shows the same principle at an exceptional tangent fiber: the lacunary natural boundary cannot be crossed by any algebraic relation with a nonexceptional Böttcher coordinate. The Hurwitz theorems show the principle in a singular arithmetic setting: quadratic relations cannot absorb noninteger branch-tail memory. The ADE theorem abstracts the differential version: a bounded finite jet plus an algebraic differential equation would force continuation across almost every good boundary point, so a bounded-jet natural boundary implies hypertranscendence.

The conjectural next step is to formalize the shared invariant. It might be a boundary groupoid, a finite-correspondence obstruction, a monodromy/tail rank, or a sheaf-theoretic continuation complexity. Whatever the right language is, the cards are already using it informally:

```text
finite relation  ⇒ finite continuation control
wild boundary    ⇒ no finite continuation control
therefore        ⇒ independence / hypertranscendence
```

That is the coherent story connecting the documents.
