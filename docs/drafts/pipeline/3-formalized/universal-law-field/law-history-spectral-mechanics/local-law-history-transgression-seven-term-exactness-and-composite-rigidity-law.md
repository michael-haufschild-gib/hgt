# Local law-history transgression, seven-term exactness, and composite rigidity law

- **ID:** ULF-LHSM-2
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM / FIRST LAW-HISTORY DIFFERENTIAL
- **Statement:** Two composable law-forming maps carry a canonical transgression from later
  erasure to earlier nonattainment. Its kernel and cokernel are exactly the two corrections needed
  to reconstruct composite failure, and the resulting seven-term sequence classifies when local
  failures cancel to an invertible total law.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [SEVEN-TERM EXACT] [COMPOSITE RIGIDITY] [INDEX CONSERVATION]
  [LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [NOT RH]

## 1. Why this is the next field law

ULF-LHSM-1 constructs the future-tail survival filtration and proves that a split
inclusion--retraction can have two nonzero local defect spaces while its total history is exact.
ULF-PSB-1 constructs the secondary birth space

\[
  Y/(\operatorname{im}f+\ker g)
\]

for two composable carriers. Those theorems identify the surviving grades but do not yet exhibit
the differential that cancels one local failure against the next.

The missing operation is forced. For

\[
 X\mathop{\longrightarrow}^{f}Y
 \mathop{\longrightarrow}^{g}Z,
 \tag{LHT.1}
\]

an element erased by the later map already lies in `Y`, so it has a canonical class modulo what
the earlier map attained:

\[
 \boxed{
 \partial_{f,g}:\ker g\longrightarrow\operatorname{coker}f,
 \qquad y\longmapsto[y].}
 \tag{LHT.2}
\]

This is the first law-history differential. It is neither selected nor fitted. It is induced by
the identity on the shared intermediate carrier.

## 2. Seven-term exactness

Let

\[
 K_f=\ker f,\quad K_{gf}=\ker(gf),\quad K_g=\ker g,
\]

\[
 C_f=Y/\operatorname{im}f,\quad
 C_{gf}=Z/\operatorname{im}(gf),\quad
 C_g=Z/\operatorname{im}g.
\]

Define the canonical maps

\[
 \begin{aligned}
 i &:K_f\to K_{gf},& i(x)&=x,\\
 a &:K_{gf}\to K_g,& a(x)&=f(x),\\
 \partial&:K_g\to C_f,& \partial(y)&=[y],\\
 b &:C_f\to C_{gf},& b([y])&=[g(y)],\\
 c &:C_{gf}\to C_g,& c([z])&=[z].
 \end{aligned}
 \tag{LHT.3}
\]

All maps are well-defined: `gf(x)=0` makes `f(x)` lie in `ker g`; `g(im f)` lies in
`im(gf)`; and `im(gf)` lies in `im g`.

### Theorem 2.1 -- local law-history exact sequence

There is a canonical exact sequence

\[
 \boxed{
 0\longrightarrow K_f\mathop{\longrightarrow}^{i}K_{gf}
 \mathop{\longrightarrow}^{a}K_g
 \mathop{\longrightarrow}^{\partial}C_f
 \mathop{\longrightarrow}^{b}C_{gf}
 \mathop{\longrightarrow}^{c}C_g\longrightarrow0.}
 \tag{LHT.4}
\]

### Proof

The map `i` is injective. At `K_(gf)`,

\[
 a(x)=0\iff f(x)=0\iff x\in K_f,
\]

so `im i=ker a`.

At `K_g`, the equality `partial(y)=0` means `y in im f`. If `y=f(x)` and `g(y)=0`,
then `gf(x)=0`, so `y=a(x)` for `x in K_(gf)`. Conversely every `a(x)=f(x)` lies in
`im f`, hence is killed by `partial`. Therefore `im a=ker partial`.

At `C_f`, suppose `b([y])=0`. Then

\[
 g(y)=gf(x)
\]

for some `x in X`. Put `k=y-f(x)`. Then `g(k)=0` and

\[
 \partial(k)=[y-f(x)]=[y].
\]

Thus `ker b subseteq im partial`; the reverse inclusion follows from `g(k)=0`.

At `C_(gf)`, suppose `c([z])=0`. Then `z=g(y)` for some `y in Y`, and

\[
 [z]=[g(y)]=b([y]).
\]

Thus `ker c=im b`. Finally every class `[z]` in `C_g` is the image under `c` of the same
representative in `C_(gf)`, so `c` is surjective. This proves exactness at every term. `square`

## 3. Kernel and cokernel of the differential

### Theorem 3.1 -- two-page reconstruction

The transgression has canonical defect descriptions

\[
 \boxed{
 \ker\partial_{f,g}\cong
 \ker(gf)/\ker f,}
 \tag{LHT.5}
\]

\[
 \boxed{
 \operatorname{coker}\partial_{f,g}\cong
 Y/(\operatorname{im}f+\ker g).}
 \tag{LHT.6}
\]

Moreover `(LHT.6)` is canonically the kernel of

\[
 C_{gf}\longrightarrow C_g.
 \tag{LHT.7}
\]

Hence one differential simultaneously reconstructs:

1. composite kernel born after the first kernel;
2. secondary carrier birth surviving later erasure;
3. the extension between secondary and outer cokernel in ULF-PSB-1.

### Proof

Exactness at `K_g` says `ker partial=im a`. The kernel of
`a:ker(gf)->ker g` is `im i`, canonically identified with `ker f`. The first isomorphism
theorem gives `(LHT.5)`.

The image of `partial` inside `C_f=Y/im f` is

\[
 (\ker g+\operatorname{im}f)/\operatorname{im}f.
\]

The third isomorphism theorem therefore gives `(LHT.6)`. Exactness at `C_(gf)` identifies the
same quotient with `ker c`, proving `(LHT.7)`. `square`

## 4. Composite rigidity

### Theorem 4.1 -- exact cancellation classification

The composite `gf:X->Z` is a linear equivalence if and only if all three conditions hold:

1. `f` is injective;
2. `g` is surjective;
3. `partial_(f,g):ker g->coker f` is a linear equivalence.

Equivalently,

\[
 \boxed{
 gf\text{ invertible}
 \iff
 f\text{ left-exact},\quad
 g\text{ right-exact},\quad
 \text{all intermediate failure cancels through }\partial.}
 \tag{LHT.8}
\]

### Proof

Assume `gf` is bijective. Then `f` is injective and `g` is surjective. If
`y in ker g` and `partial(y)=0`, write `y=f(x)`. Then `gf(x)=0`; injectivity of `gf`
gives `x=0`, hence `y=0`. Thus `partial` is injective.

For surjectivity, take `[y] in C_f`. Surjectivity of `gf` gives `x` with

\[
 gf(x)=g(y).
\]

Then `k=y-f(x)` lies in `ker g` and `partial(k)=[y]`.

Conversely assume the three displayed conditions. If `gf(x)=0`, then `f(x) in ker g` and
`partial(f(x))=0`. Injectivity of `partial` gives `f(x)=0`, and injectivity of `f` gives
`x=0`. Thus `gf` is injective.

Given `z in Z`, choose `y` with `g(y)=z`. Surjectivity of `partial` gives `k in ker g`
with `[k]=[y]`. Hence `k-y=f(x)` for some `x`; therefore

\[
 gf(-x)=g(y-k)=z.
\]

So `gf` is surjective. `square`

### Corollary 4.2 -- split transgression

If `gf=id_X`, then `f` is injective, `g` is surjective, and

\[
 \partial_{f,g}:\ker g\mathop{\longrightarrow}^{\sim}\operatorname{coker}f
 \tag{LHT.9}
\]

is a canonical equivalence. Its inverse sends `[y]` to `y-f(g(y))`. Thus ULF-LHSM-1's split
transgression is exactly the inverse of the general law-history differential.

## 5. Finite-dimensional conservation law

Assume all three vector spaces are finite-dimensional. Exactness of `(LHT.4)` gives

\[
 \begin{aligned}
 &\dim K_f-\dim K_{gf}+\dim K_g\\
 &\qquad-\dim C_f+\dim C_{gf}-\dim C_g=0.
 \end{aligned}
 \tag{LHT.10}
\]

Define

\[
 \operatorname{ind}(u)=\dim\ker u-\dim\operatorname{coker}u.
\]

Then

\[
 \boxed{
 \operatorname{ind}(gf)=\operatorname{ind}(f)+\operatorname{ind}(g).}
 \tag{LHT.11}
\]

More finely,

\[
 \dim\ker(gf)=\dim\ker f+\dim\ker\partial,
 \tag{LHT.12}
\]

\[
 \dim\operatorname{coker}(gf)
 =\dim\operatorname{coker}\partial+\dim\operatorname{coker}g.
 \tag{LHT.13}
\]

Thus the transgression conserves total defect while allowing defect type to migrate between
kernel and cokernel grades.

## 6. What this changes in the field programme

The theorem closes the first page mechanism requested by Law-History Spectral Mechanics:

```text
past nonattainment C_f
        ^
        | partial_(f,g)
        |
future erasure K_g

kernel(partial) = composite kernel born after K_f;
cokernel(partial) = secondary birth surviving before C_g.
```

This replaces four separate slogans by one law:

- **local birth is provisional:** a later kernel may cancel an earlier cokernel;
- **cancellation is typed:** it occurs through `partial`, not scalar subtraction;
- **global birth is homology:** `ker partial` and `coker partial` are the surviving defects;
- **refactorization has a differential:** inserting a stage creates the exact sequence `(LHT.4)`.

The theorem does not yet produce an RH selector. It changes the correct selection question. One
must not seek a source-native object that separately annihilates each terminal class. One must
construct a pre-divisor law history whose source-generated transgression pairs the complete later
erasure sector with the complete earlier nonattainment sector, and then prove global
formation/properness prevents an unbounded cancellation escape.

If such an arithmetic history has injective first leg, surjective last leg, and a globally proper
transgression, `(LHT.8)` upgrades local cancellation to exact total formation. The remaining RH
task is construction and positivity/properness of that literal transgression, not another endpoint
identity.

## 7. Hostile boundaries

1. **The sequence is classical.** It is the kernel--cokernel sequence of a composition and a
   special snake/octrahedral sequence. The field contribution is its use as the first constitutive
   differential joining previously separate ULF mechanisms, not a priority claim for exactness.
2. **No automatic positivity.** A linear transgression need not be positive, isometric, or closed
   after topological completion.
3. **No automatic completion exactness.** Replacing ranges by closures may insert source and target
   homology; ULF-CHM-1 is the corresponding completion warning.
4. **No scalar accumulation.** Local kernel and cokernel dimensions can both be nonzero while the
   total composite is invertible.
5. **No source theorem yet.** Defining `partial` for an already chosen pair does not construct the
   literal arithmetic pair needed for RH.

Primary parents are the explicit kernel--cokernel composition sequence
[Xiong, 2020](https://arxiv.org/abs/2001.07528), the
[snake lemma](https://stacks.math.columbia.edu/tag/07JW), and exact-couple/spectral-sequence
machinery such as [Peschke, 2022](https://arxiv.org/abs/2205.10705).

## 8. Lean boundary

Formalization must include, without axioms or placeholders:

1. all five maps in `(LHT.3)`;
2. injectivity at the left endpoint and surjectivity at the right endpoint;
3. all four range--kernel equalities in `(LHT.4)`;
4. composite-bijectivity classification `(LHT.8)`;
5. split transgression `(LHT.9)`;
6. finite-dimensional conservation `(LHT.10)--(LHT.13)` if the required quotient-finrank
   infrastructure is available without importing unrelated heavy modules.

Only this Stage-2 card is eligible for the `UniversalLawField` Lean umbrella.
