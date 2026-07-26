## What Weil actually did, mechanically

For a smooth projective curve $C$ of genus $g$ over $\mathbb{F}_q$, the zeta function is

$$Z(C,t) = \frac{P(t)}{(1-t)(1-qt)}, \qquad \deg P = 2g,$$

and RH for $C$ says every reciprocal root of $P$ has absolute value exactly $q^{1/2}$ — equivalently $|\#C(\mathbb{F}_q) - (q+1)| \le 2g\sqrt{q}$.

Weil's second proof runs on the **surface** $S = C \times_{\mathbb{F}_q} C$. Two things live there: the diagonal $\Delta$, and the graph $\Gamma_{F^n}$ of the $n$-th power of Frobenius. Since the fixed points of $F^n$ are precisely the $\mathbb{F}_{q^n}$-points of $C$, point-counting becomes an *intersection number*:

$$\#C(\mathbb{F}_{q^n}) = \Gamma_{F^n} \cdot \Delta.$$

Then comes the actual engine — the **Hodge index theorem** for surfaces. The intersection pairing on the Néron–Severi group has signature $(1, \rho - 1)$: one positive direction, everything else negative. Concretely, if $H$ is ample and $D\cdot H = 0$, then $D^2 \le 0$. Feed in suitable combinations of $\Delta$, $\Gamma_{F^n}$, and the two rulings, and this negative-definiteness yields, by a Cauchy–Schwarz-type argument, exactly the bound $2g\sqrt{q}$.

So the proof has two irreducible ingredients: **a two-dimensional object**, and **a positivity theorem on it**.

## Why $\operatorname{Spec}\mathbb{Z}$ can't play along

The dictionary is otherwise excellent. $\mathbb{F}_q[t] \leftrightarrow \mathbb{Z}$, $\mathbb{F}_q(t) \leftrightarrow \mathbb{Q}$, closed points $\leftrightarrow$ primes, and $\overline{\operatorname{Spec}\mathbb{Z}}$ (with the archimedean place adjoined, matching the $\Gamma$-factor) plays the role of the compact curve.

But $C$ is a curve *relative to a base* $\operatorname{Spec}\mathbb{F}_q$, which is a point; that relative dimension is what makes $C\times C$ two-dimensional. And $\operatorname{Spec}\mathbb{Z}$ is the terminal object in schemes — there is nothing beneath it. So

$$\operatorname{Spec}\mathbb{Z}\times_{\operatorname{Spec}\mathbb{Z}}\operatorname{Spec}\mathbb{Z} = \operatorname{Spec}(\mathbb{Z}\otimes_{\mathbb{Z}}\mathbb{Z}) = \operatorname{Spec}\mathbb{Z}.$$

The product collapses. You get a curve, not a surface. No intersection theory, no Hodge index, no proof. The entire $\mathbb{F}_1$ program is an attempt to manufacture a base *below* $\operatorname{Spec}\mathbb{Z}$ so that $\mathbb{Z}\otimes_{\mathbb{F}_1}\mathbb{Z}$ is genuinely larger.

## Why anyone believes such a base exists

The evidence is a family of $q \to 1$ degenerations that are too clean to be coincidence. Tits noticed in 1957 that the Grassmannian point-count $\binom{n}{k}_q$ specializes at $q=1$ to $\binom{n}{k}$ — as if "vector spaces over $\mathbb{F}_1$" were finite sets, subspaces were subsets, and $GL_n(\mathbb{F}_1) = S_n$. Likewise $\#\mathbb{P}^{n-1}(\mathbb{F}_q) \to n$. Manin (1995) and Smirnov pushed this toward zeta functions: if $\operatorname{Spec}\mathbb{Z}$ were an $\mathbb{F}_1$-curve, one should be able to write $\zeta(s)$ in Weil form and find an "absolute Frobenius."

Of course $\mathbb{F}_1$ cannot literally be a field ($0 \ne 1$ forces at least two elements), so every formalism replaces "field" with something weaker — monoids, pointed sets, monads, blueprints, or the Boolean semifield $\mathbb{B} = \{0,1\}$ with $1+1=1$.

## What the framework would have to deliver

Not just a definition of $\mathbb{F}_1$-schemes, but on $\overline{\operatorname{Spec}\mathbb{Z}}\times_{\mathbb{F}_1}\overline{\operatorname{Spec}\mathbb{Z}}$: cycles and a real-valued intersection pairing; a diagonal and a family of Frobenius correspondences; a Lefschetz trace formula; and a Hodge-index-style positivity.

Two of these are already partly visible unconditionally, which is the real reason the picture is taken seriously. Weil's **explicit formula** genuinely has the shape of a Lefschetz trace formula — Connes made this precise by showing RH is equivalent to a trace formula on the adele class space. And since $\mathbb{F}_1$ has no $q$, Frobenius can't act in discrete powers; it becomes a **continuous flow**, with "eigenvalues of Frobenius" becoming a spectrum. That is not a separate problem from Hilbert–Pólya — it's the same problem in different clothes, which is a point in favor of both.

## The formalisms, and where each stops

- **Deitmar** (monoid schemes) is the cleanest, and comes with a no-go theorem: what it produces is essentially toric geometry, and $\operatorname{Spec}\mathbb{Z}$ isn't of finite type over it. Useful mainly as a proof that naive approaches are too rigid.
- **Soulé** gave the first serious definition via functorial "gadgets"; **Lorscheid**'s blueprints subsume this and recover Chevalley groups with Weyl-group point sets — i.e., they successfully explain the Tits phenomena, which is not the same as producing an arithmetic surface.
- **Toën–Vaquié** do relative geometry over a symmetric monoidal category, with $\mathbb{F}_1$ = geometry over $(\mathrm{Set},\times)$. Structurally elegant, arithmetically inert so far.
- **Borger** identifies descent to $\mathbb{F}_1$ with a $\Lambda$-ring structure — commuting Frobenius lifts at every prime. Conceptually the most satisfying answer to "where does Frobenius come from," and $\mathbb{Z}$ does descend. But no intersection theory with positivity has come out of it.
- **Durov** (generalized rings as monads) and **Haran** aim squarely at compactification and Arakelov theory, trying to make the archimedean place algebraic rather than a bolted-on analytic correction.
- **Connes–Consani** is the line explicitly engineered for RH: the Arithmetic Site and then the **Scaling Site**, a curve over $\mathbb{B}$ carrying an $\mathbb{R}_+^\times$-flow. They obtain a Riemann–Roch theorem in characteristic 1, and the periodic orbits reproduce the Riemann–von Mangoldt counting function. This is the furthest anyone has gotten. What remains missing is precisely the positivity — and in their setting Weil positivity is still *equivalent* to RH, not derived.

## The obstructions, stated plainly

Manin's observation is the sharpest: $\zeta(s)$ has infinitely many zeros, so the analogue of $H^1$ must be infinite-dimensional — $\operatorname{Spec}\mathbb{Z}$ behaves as a curve of infinite genus. Hodge index theorems are theorems about finite-dimensional lattices with a signature condition; in infinite dimensions, positivity results of this strength are rare and delicate, and there's no reason to expect a routine generalization.

Second, characteristic 1 has no subtraction. Idempotent semirings don't form abelian categories, so derived functors, exact sequences, and essentially all standard homological machinery are unavailable and must be rebuilt from nothing.

Third — the honest caveat — nobody has shown that a satisfactory $\mathbb{F}_1$-geometry would actually *imply* RH. The function-field proof leans on finite-dimensionality at several points beyond the ones usually advertised. It is entirely possible to build the surface and still find the positivity statement exactly as hard as it was before, which is roughly what has happened at each stage so far: the framework reproduces the phenomena we already knew, and stalls at the one inequality that was the whole point.