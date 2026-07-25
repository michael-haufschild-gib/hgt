# Local cyclotomic detection of the Euler product

- **ID:** `local-cyclotomic-detection-of-the-euler-product`
- **Stage:** 1-in-progress (Theorems 1–5 proved; main conjecture open)
- **Type:** THEOREM (paper + Lean) + `[CONJECTURE]` with a named `[OPEN CORE]`
- **Lane:** upstream structure of degree-one L-functions; the discrete invariant behind
  "Euler product ⟹ RH"
- **Parents:**
  - `1-in-progress/euler-defect-controls-displacement.md` (§ "Steering": *the mechanism by which
    multiplicativity forces the critical line is arithmetic discreteness, not analytic size*;
    the immediate finite task named there is answered in part here)
  - `5-failed/downstream-functionals-of-the-zero-set.md` (rule: a statement is worth pursuing only
    if it is **upstream** of the zeros and **not equivalent to RH**)
- **Lean:** `formal/GaloisForLFunctions/RHTower/PeriodicLocalVonMangoldt.lean`
  (builds, axioms exactly `propext, Classical.choice, Quot.sound`)

---

## 0. Why this object

Two corpus results fix the direction.

1. `euler-defect-controls-displacement.md` **falsified** every attempt to control zero displacement
   by an *analytic size* measure of non-multiplicativity: displacement responds to a coefficient
   perturbation like `1/|L'(rho)|`, which is unbounded, so no norm on the coefficients that is
   continuous under `L ↦ L + eps·g` can work. Its successor statement: *any proof of
   "Euler product ⟹ RH" must use a feature of multiplicativity that is **discontinuous** in the
   coefficients.* It named the candidate — discreteness of the value set of the coefficients of
   `-L'/L` — and left as the immediate finite task: *construct or exclude a non-multiplicative `L`
   with a zeta-type functional equation and discrete `b_n`.*
2. `downstream-functionals-of-the-zero-set.md` forbids any further `RH ⟺ X`.

This card supplies the exact discrete invariant, prime by prime, and reduces the finite task to a
finite algebraic condition. Nothing here is a functional of the zero set; everything is a statement
about the coefficient sequence, which is what *produces* the zeros.

**Parent theory used.** `[LITERATURE]` Kaczorowski–Perelli, *On the structure of the Selberg class,
I: 0 ≤ d ≤ 1*, Acta Math. **182** (1999), 207–241: every element of the **extended** Selberg class
`S^#` of degree one is, up to a single vertical shift `s ↦ s + i·theta` forced by the imaginary part
of the gamma-factor parameter `mu`, a Dirichlet series with **periodic** coefficients

  `F(s) = sum_{n>=1} alpha(n) n^{-s-i theta}`,  `alpha` periodic mod `q`,  `alpha(1) = 1`,

and the functional equation is exactly the statement that the vector `alpha` is an eigenvector of
the finite Fourier transform on `Z/q` (a Gauss-sum condition; Dirichlet characters are the
eigenvectors coming from Euler products, Davenport–Heilbronn mod 5 is an eigenvector that is not).
`[LITERATURE]` Saias–Weingartner: a periodic Dirichlet series that is not `P(s)L(s,chi)` has
infinitely many zeros in `sigma > 1`; so in degree one "no zeros right of 1" already **is** the
Euler product. The open question is the analogous statement at `1/2`.

---

## 1. The virtual local polynomial

Fix `F` as above with `theta = 0` for the moment, `alpha` periodic mod `q`, `alpha(1)=1`. Write

  `log F(s) = sum_{n>=2} c_n n^{-s}`,  `-F'/F(s) = sum_{n>=2} b_n n^{-s}`,  `b_n = c_n log n`.

Because a factorisation of `p^m` uses only powers of `p`, the coefficient `c_{p^m}` depends only on
the *local* data `(alpha(p^i))_{i>=0}`. For `p` coprime to `q` with `d = ord_q(p)` the sequence
`i ↦ alpha(p^i)` is `d`-periodic, so its generating function is rational:

  `G_p(X) = sum_{i>=0} alpha(p^i) X^i = N_p(X) / (1 - X^d)`,
  **`N_p(X) := sum_{i=0}^{d-1} alpha(p^i) X^i`,  `N_p(0) = 1`.**

`N_p` is the **virtual local polynomial** of `F` at `p`. If `F` has an Euler product then
`G_p(X) = 1/(1 - alpha(p) X)` is the genuine local factor; in general `G_p` is not a factor of `F`
at all, but it is exactly what the prime-power coefficients of `-F'/F` see.

---

## 2. Theorem 1 — the local von Mangoldt formula `[PROVED HERE]`

Let `r_1, …, r_e` be the roots of `N_p` (all nonzero, since `N_p(0)=1`) and set the reciprocal-root
power sums `pi_k := sum_j r_j^{-k}`.

> **Theorem 1.** For every `k >= 1`,
>
>   **`b_{p^k} = ( d · [ d | k ] − pi_k ) · log p`.**

*Proof.* `c_{p^k} = [X^k] log G_p = [X^k]( log N_p − log(1 − X^d) )`. Writing
`N_p(X) = prod_j (1 − X/r_j)` (legitimate because `N_p(0)=1`),
`log N_p = − sum_k (pi_k/k) X^k`, while `−log(1−X^d) = sum_{m>=1} X^{dm}/m` contributes `d/k` at
`X^k` exactly when `d | k`. Hence `c_{p^k} = (d[d|k] − pi_k)/k` and `b_{p^k} = k c_{p^k} log p`. ∎

*Consistency.* For `alpha = chi` a Dirichlet character, `N_p(X) = (1 − X^d)/(1 − chi(p)X)`, whose
reciprocal roots are the `d`-th roots of unity other than `chi(p)`; then
`pi_k = d[d|k] − chi(p)^k` and Theorem 1 returns `b_{p^k} = chi(p^k) log p = Lambda(p^k)chi(p^k)`.
For `q = 1` it returns `b_{p^k} = log p = Lambda(p^k)`.

**Reading.** The local von Mangoldt data splits into a *universal cyclotomic term* `d·[d|k]`, fixed
by the period alone, plus the power sums of the reciprocal roots of a finite polynomial. All the
arithmetic of `F` at `p` sits in the root locus of `N_p`.

**Lean.** `RHTower.isLocalVonMangoldt_iff_isRecipPowerSum` (the decomposition, stated as an exact
equivalence between the two convolution normalisations, no root theory needed) together with
`RHTower.isRecipPowerSum_recipFactor` (the sequence so characterised *is* the power-sum sequence of
the reciprocal roots) and `RHTower.isLocalVonMangoldt_unique`.

---

## 3. Theorem 2 — the local discreteness dichotomy `[PROVED HERE]`

> **Theorem 2.** For `p` coprime to `q`, the set `B_p := { b_{p^k} : k >= 1 }` is **finite** if and
> only if every root of `N_p` is a root of unity. If some root is not a root of unity then either
> `|b_{p^k}| → ∞` (some root lies strictly inside the unit disc) or `B_p` is bounded with a finite
> accumulation point; in the latter case `B_p` is not discrete.

*Proof.* Put `y_j = 1/r_j`, so `pi_k = sum_j y_j^k`.

*(a) Finite ⟹ bounded ⟹ `max|y_j| <= 1`.* If `B_p` is finite then `(pi_k)` takes finitely many
values, hence is bounded, hence `sum_k pi_k z^k = sum_j y_j z/(1 − y_j z)` has radius of convergence
`>= 1`. But that rational function has a pole at `z = 1/y_j` for every distinct `y_j` (residues of
equal `y_j` add with positive multiplicity, so no cancellation), and `|1/y_j| < 1` whenever
`|y_j| > 1`. Hence `|y_j| <= 1` for all `j`.

*(b) The unit-modulus part must be torsion.* Split `pi_k = sigma(k) + tau(k)` with
`sigma(k) = sum_{|y_j| = 1} y_j^k` and `tau(k) = sum_{|y_j| < 1} y_j^k → 0`. Suppose some
unit-modulus `y_j` is not a root of unity. By Kronecker–Weyl the vector `(y_1^k, …, y_m^k)` over the
unit-modulus indices equidistributes in the closed subgroup `H` they generate, which then has
positive dimension; the sum map is non-constant on a positive-dimensional subtorus (a relation
`sum_l c_l t^{a_l} ≡ const` forces all `a_l = 0`), so the closure of `{sigma(k)}` is infinite. Since
`pi_k = sigma(k) + o(1)` and `sigma` returns arbitrarily close to every point of its infinite closure
at arbitrarily large `k`, `pi_k` cannot take only finitely many values. Contradiction.

*(c) No roots strictly inside.* Now `sigma` is periodic, with finite value set `V`. If some
`|y_j| < 1` then `tau ≢ 0` (distinct `y_j` give linearly independent exponential sequences), so
`tau(k) ≠ 0` for infinitely many `k`, while `tau(k) → 0`. Finiteness of `{pi_k}` forces
`tau(k) ∈ ({pi_k}-values) − V`, a fixed finite set; combined with `tau(k) → 0` this makes
`tau(k) = 0` for all large `k`, hence `tau ≡ 0` — contradiction. So no root of `N_p` lies outside
the closed unit disc for `1/r`, i.e. every root of `N_p` is a root of unity.

The converse is immediate: all `y_j` roots of unity makes `pi` periodic, so
`b_{p^k}/log p = d[d|k] − pi_k` is periodic and `B_p` is finite. ∎

**Lean (converse direction, and its consequence).** `RHTower.periodic_of_periodic_recipPowerSum`
and `RHTower.finite_range_of_periodic`.

**Reading.** *Multiplicativity of `F` at `p` is a torsion condition, not a size condition.* The
condition `|r_j| >= 1` is exactly the local Ramanujan bound; being a **root of unity** is Ramanujan
plus torsion, and torsion is discontinuous in the coefficients — a root of unity cannot be perturbed
to a nearby root of unity. This is the discontinuous invariant that
`euler-defect-controls-displacement.md` predicted must exist.

---

## 4. Theorem 3 — Euler factor criterion `[PROVED HERE]` `[LEAN]`

> **Theorem 3.** `F` has a genuine Euler factor at `p` (i.e. `alpha(p^i) = alpha(p)^i` for all `i`)
> **iff** `N_p(X) · (1 − alpha(p) X) = 1 − X^d`, **iff** `b_{p^k} = alpha(p)^k log p` for all `k`.
> Equivalently: the reciprocal roots of `N_p` are precisely the `d`-th roots of unity other than
> `alpha(p)`.

*Proof.* `G_p = 1/(1 − cX)` with `c = alpha(p)` forces `c^d = alpha(p^d) = alpha(1) = 1`, and
`N_p = (1 − X^d)G_p = (1 − X^d)/(1 − cX)`. Conversely a geometric local sequence is characterised by
its local von Mangoldt sequence being geometric: from `k a_k = sum_{j=1}^{k} c^j a_{k-j}` with
`a_0 = 1`, induction gives `a_k = c^k`, and the converse computation is
`sum_{j=1}^{k} c^j c^{k-j} = k c^k`. ∎

**Lean.** `RHTower.geometric_vonMangoldt_iff`, `RHTower.periodicCoeff_geometric_iff`,
`RHTower.isLocalVonMangoldt_geometric_iff`.

---

## 5. Theorem 4 — a nonzero shift destroys discreteness `[PROVED HERE]`

> **Theorem 4.** If `theta ≠ 0` then `{b_n}` is not discrete.

*Proof.* With the shift, `b_{p^k}` is multiplied by `p^{-ik theta}`. Since `log p` for distinct `p`
are `Q`-linearly independent, at most one prime can satisfy `theta log p ∈ 2 pi Q`; choose any other
`p` coprime to `q` with `alpha(p) ≠ 0`. Then `k ↦ p^{-i k theta}` is dense on the unit circle and the
values `b_{p^k}` accumulate on the whole circle of radius `|·| log p`, a bounded set. ∎

So discreteness already pins `theta = 0`, i.e. no vertical shift.

---

## 6. Theorem 5 — coupled cyclotomic rigidity in order three `[PROVED HERE]`

The condition of Theorem 2 must hold simultaneously at **every** generator of a cyclic subgroup,
because by Dirichlet every residue class coprime to `q` contains infinitely many primes. Write
`u ∈ (Z/q)^×` of order `d`, `v_i := alpha(u^i)`, `v_0 = 1`, and
`N^{(j)}(X) := sum_{i<d} v_{ij mod d} X^i` for `gcd(j,d) = 1`.

> **Theorem 5.** Let `d = 3` and `v_1 v_2 ≠ 0`. If both `N^{(1)}` and `N^{(2)}` have all roots roots
> of unity, then `alpha` restricted to `⟨u⟩` is a cubic character.

*Proof.* Write `N^{(1)} = (1 − y_1 X)(1 − y_2 X)`, `N^{(2)} = (1 − z_1 X)(1 − z_2 X)` with all
`y_i, z_i` roots of unity. Then `v_1 = −(y_1 + y_2)`, `v_2 = y_1 y_2`, and also
`v_2 = −(z_1 + z_2)`, `v_1 = z_1 z_2`. From `|v_2| = 1` we get `|z_1 + z_2| = 1`, so `z_2 = z_1 w`
with `w` a primitive cube root of unity (up to conjugation); likewise `y_2 = y_1 w^{eps}`,
`eps = ±1`. Substituting, `v_1 = y_1 w^{-eps} = z_1^2 w` and `v_2 = y_1^2 w^{eps} = z_1 w^2`.
Eliminating `z_1` gives `y_1 w^{-eps} = y_1^4 w^{2eps}`, i.e. `y_1^3 = 1`. Hence
`{y_1,y_2} ⊂ {1,w,w^2}` and the three possible pairs give `(v_1,v_2) ∈
{(w^2,w), (w,w^2), (1,1)}` — in each case `v_2 = v_1^2`, so `alpha|⟨u⟩` is a character. ∎

*Degeneracies are real.* Without `v_1 v_2 ≠ 0` the conclusion fails: `v_1 = v_2 = 0` gives
`N^{(1)} = N^{(2)} = 1`, no roots, so the cyclotomic condition holds vacuously while `alpha` is not a
character. Likewise for `d = 2` the condition only forces `alpha(u)` to be **some** root of unity,
whereas a character needs `alpha(u) = ±1`; e.g. `alpha(u) = i` passes the local test. In both cases
the missing constraint has to come from the functional equation, not from the local data.

**Worked check that the functional equation does bite.** Modulus `q = 3`. Here
`(Z/3)^× = {1,2}` with `2` of order `2`, and the FE eigenvector condition is
`(1/√3)·DFT(alpha) = eps·alpha`. Setting `alpha(2) = i` (allowed by the local test), the first two
eigen-equations force `alpha(0) = −w^2(1+i)` and `eps = i` with `w = e^{2 pi i/3}`; the third
eigen-equation then demands `(1+i)e^{i pi/6} = (1+i)e^{5 i pi/6}`, which is false. So `alpha(2) = i`
is **not** realisable mod 3: the FE kills the local degeneracy in this case.

---

## 7. The conjecture

> **[CONJECTURE — Discreteness rigidity in degree one]** Let `F` belong to the extended Selberg
> class with `d_F = 1` and `a_1(F) = 1`. If the value set `{b_n : n >= 2}` of the coefficients of
> `-F'/F` is **discrete in C** (no accumulation point in `C`), then `F(s) = L(s, chi)` for a
> Dirichlet character `chi`; in particular `F` has an Euler product.

By Theorems 1–5 the conjecture is equivalent, at the prime-power level, to:

> **[OPEN CORE]** Let `alpha` be a periodic function mod `q` with `alpha(1) = 1` which is an
> eigenvector of the finite Fourier transform on `Z/q` (the degree-one functional equation). Suppose
> that for **every** residue `u` coprime to `q` and every generator `u^j` of `⟨u⟩` the polynomial
> `sum_{i<d} alpha(u^{ij}) X^i` has all its roots roots of unity. Then `alpha` restricted to
> `(Z/q)^×` is a Dirichlet character.

Theorem 5 proves the order-three non-degenerate case of the open core; the §6 computation shows the
FE eigenvector condition is what removes the order-two and vanishing degeneracies. What is *not*
proved is the passage from the local cyclotomic conditions at all primes, together with the FE, to
global multiplicativity; and the composite coefficients `b_n` for `n` with two or more prime factors
are not yet used at all (they carry the genuinely non-local information
`b_{pq} = (alpha(pq) − alpha(p)alpha(q)) log(pq)`).

### What is structurally new

The Euler product, inside the only class where the functional equation is completely classified, is
identified with a **torsion condition on the root locus of an explicit finite polynomial attached to
each prime**. This is a *discontinuous* invariant of the coefficients, of exactly the kind the
falsification in `euler-defect-controls-displacement.md` proved is necessary, and it is invisible to
every `ℓ^1`/`ℓ^2` measure of the Euler defect.

### How it could fail

Exhibit a periodic FE eigenvector `alpha`, not a character, with all `N^{(j)}` cyclotomic and with
locally finite composite coefficients. Theorem 5's degenerate cases (`alpha` vanishing on units;
order-two subgroups) are the places to look; §6 shows the FE closes the smallest such case, but this
is not a proof.

### What its truth would open

A dichotomy inside degree one that is entirely coefficient-side and entirely discrete:

- `{b_n}` discrete ⟺ Euler product ⟺ zero-free in `sigma > 1` (Saias–Weingartner);
- `{b_n}` non-discrete ⟹ (known in the Davenport–Heilbronn cases) `≫ T` zeros in `sigma > 1`.

The Riemann Hypothesis for degree one would then be the statement that the same discrete invariant
also controls `sigma > 1/2`; and the search for the proof mechanism moves from analytic size to the
arithmetic of roots of unity. That relocation is the point of this card, not a proof of RH.

---

## 8. Anti-collision record

- Internal: `scripts/formal_tools.py research "periodic Dirichlet coefficients local von Mangoldt
  logarithmic derivative recursion"` and `"power sums reciprocal roots polynomial periodic sequence
  convolution identity"` — no theorem of this shape exists in the tree; the nearest declarations are
  von-Mangoldt carriers for `zeta` itself.
- External: searches over "logarithmic derivative of Dirichlet series with periodic coefficients",
  "Euler product characterisation", "power sums local polynomial", "Davenport–Heilbronn coefficient
  formulas" returned value-distribution and universality theory for periodic Dirichlet series
  (Steuding; Laurinčikas–Matsumoto) and generalised von Mangoldt functions for *multiplicative* `f`
  only. No collision found with Theorems 1–3; no priority claim is made.
- Parent theories used and credited: Kaczorowski–Perelli degree-one structure; Saias–Weingartner;
  Kronecker–Weyl equidistribution; Newton's identities.

## Gates

- [x] 0 → 1: exact discrete invariant isolated; parent theory identified
- [x] Theorems 1–5 proved on paper with no open dependency
- [x] Theorem 1 (decomposition), Theorem 3 (Euler factor), reciprocal-root identification,
      uniqueness and the torsion ⟹ finiteness direction formalised in Lean, axiom-clean
- [ ] `[OPEN CORE]`: FE eigenvector + all-prime cyclotomic ⟹ character
- [ ] Composite coefficients `b_{n}` for `n` with ≥ 2 prime factors brought into the argument
- [ ] 1 → 2: complete unconditional proof of the conjecture

## Log

- 2026-07-25 — Theorems 1–5 proved; Lean module `PeriodicLocalVonMangoldt.lean` built and
  axiom-audited (`propext, Classical.choice, Quot.sound`); wired into `RHTower.lean`.

---

## 9. Cycle 2 — the composite coefficients carry no extra discreteness information

The open core asks whether the local cyclotomic conditions plus the functional equation force
multiplicativity. Before assuming so, one must check whether the **composite** coefficients `b_n`
(for `n` with two or more distinct prime factors) impose further constraints. Along every slice they
do not, and the reason is structural.

### 9.1 The two-prime generating function is rational `[PROVED HERE]`

Fix distinct primes `p, r` coprime to the modulus `Q`, with orders `d_p, d_r` in `(Z/Q)^×`. A
factorisation of `p^i r^j` uses only numbers of the form `p^a r^b`, so

  `sum_{i,j >= 0} c_{p^i r^j} X^i Y^j = log G_{p,r}(X, Y)`,
  `G_{p,r}(X,Y) := sum_{i,j >= 0} alpha(p^i r^j) X^i Y^j`.

Since `alpha(p^i r^j)` depends only on `(i mod d_p, j mod d_r)`, the array is doubly periodic and

  `G_{p,r}(X,Y) = N_{p,r}(X,Y) / ((1 - X^{d_p})(1 - Y^{d_r}))`

with `N_{p,r}` of bidegree `< (d_p, d_r)` and `N_{p,r}(0,0) = 1`. Setting `Y = 0` recovers
`N_{p,r}(X,0) = N_p(X)`, and by symmetry `N_{p,r}(0,Y) = N_r(Y)`.

*Consistency.* If `alpha` is a character then `G_{p,r}(X,Y) = 1/((1-chi(p)X)(1-chi(r)Y))` factors,
`log G` is a sum of a function of `X` and a function of `Y`, and `c_{p^i r^j} = 0` for `i, j >= 1` —
exactly the statement that the von Mangoldt coefficients are supported on prime powers.

### 9.2 The `Y`-slices have poles only at the roots of `N_p` `[PROVED HERE]`

Write `N_{p,r}(X,Y) = sum_j N_j(X) Y^j`, so `N_0 = N_p`. Then

  `log N_{p,r} = log N_p + log( 1 + sum_{j>=1} (N_j/N_p) Y^j )`,

and expanding the outer logarithm shows that `[Y^j] log G_{p,r}` is a rational function of `X` whose
denominator divides `N_p(X)^j`. **Every pole of every `Y`-slice is a root of `N_p`.**

### 9.3 Local torsion propagates to the composite coefficients `[PROVED HERE]`

Suppose every root of `N_p` is a root of unity (the discreteness condition of Theorem 2). Then for
each fixed `j`, partial fractions give

  `c_{p^i r^j} = sum_l P_l(i) zeta_l^{-i}`,  `zeta_l` roots of unity, `P_l` polynomials,

a **quasi-polynomial** in `i`: on each residue class modulo the common order of the `zeta_l` it is a
polynomial in `i`. Therefore on each residue class it is either identically zero or bounded below in
absolute value for large `i`, so

  `b_{p^i r^j} = c_{p^i r^j} · (i log p + j log r)`

is either `0` or tends to infinity in modulus as `i → ∞`. **No accumulation point arises from a
fixed `Y`-slice**, and symmetrically none from a fixed `X`-slice.

### 9.4 What this settles, and what it leaves

- `[SETTLED]` Two-prime coefficients are useless for discreteness:
  `b_{pr} = (alpha(pr) - alpha(p)alpha(r)) log(pr)` and the bracket takes finitely many values, so
  `|b_{pr}|` is `0` or `>= delta · log(pr) → ∞`. By §9.3 the same holds along every fixed slice.
  Discreteness imposes **no** condition beyond the prime-power one along slices.
- `[OPEN, SHARPENED]` The only remaining possibility is a genuinely two-dimensional family: a
  sequence `(i_t, j_t)` with both coordinates unbounded along which `c_{p^{i_t} r^{j_t}}` decays like
  `1/(i_t log p + j_t log r)`. For rational `G_{p,r}` the coefficient asymptotics in a direction
  `(a,b)` are governed by the **amoeba** of `N_{p,r}`: exponential decay in a direction occurs
  exactly when the origin component of the amoeba complement extends beyond the unit torus in that
  direction. So:

  > **[OPEN CORE, two-variable form]** If every root of `N_p` and of `N_r` is a root of unity, must
  > the zero curve `{N_{p,r} = 0} ⊂ (C^*)^2` meet the unit torus in every direction of its Newton
  > polygon?

  This is the two-variable analogue of "roots on the unit circle", and it sits in the regime of
  **Laurent's theorem** (Mordell–Lang / Manin–Mumford for tori): a subvariety of `(C^*)^n`
  containing a Zariski-dense set of torsion points is a finite union of torsion cosets. If the
  torsion conditions at `p` and at `r` force the zero curve of `N_{p,r}` to be a union of torsion
  cosets, the composite coefficients are quasi-polynomial in **both** variables and discreteness is
  *equivalent* to the prime-power condition, with no residual information.

### 9.5 Steering after cycle 2

The discreteness invariant is **purely local** (prime-power) as far as any slice can see. The
rigidity therefore cannot come from the composite coefficients; it must come from the **functional
equation**, which is the only mechanism coupling the local polynomials `N_p` across residue classes
— the finite-Fourier eigenvector condition ties `alpha` on all of `Z/Q` at once, whereas the
cyclotomic conditions are one cyclic subgroup at a time. The §6 computation modulo 3 is the smallest
instance of that coupling doing the work. Next target: prove

  > FE eigenvector + all `N^{(j)}` cyclotomic ⟹ `alpha|(Z/Q)^×` is a Dirichlet character,

first for `Q` prime, where `(Z/Q)^×` is cyclic, so the cyclotomic conditions at all `phi(Q)`
generators together with one Gauss-sum identity are the entire content.

---

## 10. Cycle 3 — the discreteness conjecture of §7 is FALSE, and the repaired invariant

Preparing the two-variable analysis exposed an error of level in §7: **discreteness of a set is local
finiteness, which is strictly weaker than finiteness.** Theorem 2 characterises when `B_p` is
*finite*; a `B_p` whose values escape to infinity is infinite but still discrete. The conjecture of
§7 assumed the wrong one. Correcting this kills it.

### 10.1 Theorem 6 — the exact local discreteness trichotomy `[PROVED HERE]`

With `y_j = 1/r_j` the reciprocal roots of `N_p` and `pi_k = sum_j y_j^k`:

> **Theorem 6.** `B_p = {b_{p^k}}` is
> 1. **finite** iff every `y_j` is a root of unity (Theorem 2);
> 2. **infinite but discrete** whenever `max_j |y_j| > 1` and the dominant exponential sum does not
>    return to a bounded region infinitely often — in particular whenever there is a unique root of
>    maximal modulus, since then `|pi_k| → ∞`;
> 3. **not discrete** when `max_j |y_j| <= 1` and some `y_j` is not a root of unity: then `pi_k` is
>    bounded and takes infinitely many values, so `B_p` accumulates. In particular `B_p` is not
>    discrete when **all** roots of `N_p` lie strictly outside the closed unit disc, where
>    `pi_k → 0` with `pi_k ≠ 0` infinitely often, so `B_p` accumulates at `d·[d|k]·log p`.

Cases 1 and 3 are exactly the two halves of the proof of Theorem 2; case 2 is the new one and is
where the counterexample lives.

### 10.2 The Davenport–Heilbronn function is a counterexample `[FALSIFIES §7]`

Take the modulus `Q = 5`, `chi` the quartic character with `chi(2) = i`. The odd functions on
`Z/5` supported on the units are spanned by `chi` and `chi-bar`, so every FE eigenvector of that
parity is `alpha = (1, xi, -xi, -1, 0)` on residues `(1,2,3,4,0)` for a real `xi`, with
`alpha = c_1 chi + c_3 chi-bar`, `c_1 = (1 - i xi)/2`, `c_3 = (1 + i xi)/2`.

The eigenvector equations `-c_3 \bar u = eps c_1`, `c_1 u = eps c_3` with `u = tau(chi)/sqrt5` give
`eps^2 = -1`, i.e. `eps = ± i`, and

  `(1 - i xi)/(1 + i xi) = eps / u`,  hence  `xi = -tan(phi/2)`,  `e^{i phi} = eps / u`.

Both signs of `eps` occur. Replacing `eps` by `-eps` sends `phi` to `phi + pi` and hence
`xi = -tan(phi/2)` to `-1/xi`: the two resulting functions are the two Davenport–Heilbronn functions
with opposite root numbers, and their parameters are **reciprocal**, `xi' = -1/xi`.

Two exact facts are all that is needed, and no numerics enter.

- **`|xi| ≠ 1`.** `|xi| = |tan(phi/2)| = 1` iff `phi ≡ ± pi/2 (mod 2 pi)`, iff `e^{i phi} = ± i`,
  iff `eps/u = ± i`, iff `u = ± 1` (as `eps = ± i`), iff the Gauss sum `tau(chi)` is real. But
  `tau(chi) = sum_{n=1}^{4} chi(n) e(n/5) = -2 sin(4 pi/5) + 2 i sin(2 pi/5)` has imaginary part
  `2 sin(2 pi/5) ≠ 0`. So `|xi| ≠ 1`.
- **Exactly one branch has `|xi| > 1`**, since the two parameters are `xi` and `-1/xi` and
  `|xi| ≠ 1`.

Also `xi` is real (`phi` is real), and `alpha` is not multiplicative: `alpha(2)^2 = xi^2 >= 0` while
`alpha(4) = -1`. By Saias–Weingartner both branches therefore have infinitely many zeros with
`sigma > 1`.

Now take the branch with `|xi| > 1` and compute the local polynomials.

| `p mod 5` | `d` | `N_p(X)` | roots | reciprocal roots | `B_p` |
|---|---|---|---|---|---|
| `1` | 1 | `1` | none | none | `{log p}` finite |
| `2` | 4 | `(1-X^2)(1+xi X)` | `±1, -1/xi` | `1, -1, -xi` | `pi_k → ∞`, **discrete** |
| `3` | 4 | `(1-X^2)(1-xi X)` | `±1, 1/xi` | `1, -1, xi` | `pi_k → ∞`, **discrete** |
| `4` | 2 | `1 - X` | `1` | `1` | `{± log p}` finite |
| `p = 5` | — | `alpha(5^i) = 0` for `i>=1` | — | — | `{0}` |

Since `|xi| > 1`, the root `∓1/xi` lies strictly **inside** the unit disc, so the reciprocal root
`∓xi` has modulus `> 1` and is the unique dominant one; hence `|pi_k| → ∞` and `B_p` is discrete for
every prime. By §9.2–9.3 every fixed slice of the composite coefficients has poles only at roots of
`N_p`, so it also grows or vanishes; and for the mixed case `p ≡ 2`, `r ≡ 4` one has the exact
closed form

  `c_{p^i r^j} = ((-1)^{j+1}/j) · [X^i] (M_1/N_p)^j`,  `N_{p,r}(X,Y) = N_p(X) + Y M_1(X)`,

with `M_1` the two-step cyclic shift of `N_p`'s coefficient vector; because `|M_1(0)| = |alpha(4)| =
1` and `N_p` has a root inside the unit disc, these grow in `i` and are only polynomially controlled
in `j` — no exponential decay, hence no accumulation.

> **`[FALSIFIED]`** The conjecture of §7 is false. There is a degree-one element of the extended
> Selberg class with a zeta-type functional equation, **without** an Euler product, whose
> logarithmic-derivative coefficient set `{b_n}` is discrete — and which has infinitely many zeros
> with `sigma > 1`, hence very far off the critical line.

This **answers the immediate finite task** posed in
`euler-defect-controls-displacement.md`: *"Constructing or excluding such an `L` is the immediate
finite task."* The object exists. Discreteness of the value set of `{b_n}` is therefore **not** the
discontinuous invariant behind "Euler product ⟹ RH".

### 10.3 The repaired invariant

What Davenport–Heilbronn violates is not discreteness but **per-prime finiteness**, equivalently
(Theorem 2) the cyclotomic condition. So the corrected statement is:

> **[CONJECTURE — Local torsion rigidity in degree one]** Let `F` be a degree-one element of the
> extended Selberg class with `a_1(F) = 1`. If for **every** prime `p` the set
> `{b_{p^k} : k >= 1}` is *finite*, then `F(s) = L(s, chi)` for a Dirichlet character `chi`.

By Theorems 1–2 this is exactly the `[OPEN CORE]` of §7 (all `N_p` cyclotomic + FE ⟹ character),
now with the hypothesis stated at the right strength, and with Davenport–Heilbronn no longer a
threat: its `N_p` at `p ≡ 2, 3 (mod 5)` has the non-torsion root `∓1/xi`, so its `B_p` is infinite.

The invariant is now sharply **two-tiered**, and the tiers are exactly the two classical local
conditions:

- `|r| >= 1` for every root of `N_p` — the local **Ramanujan** condition. Davenport–Heilbronn
  *violates* this at `p ≡ 2, 3 (mod 5)` for the branch `|xi| > 1`, and violates the reflected
  condition for the branch `|xi| < 1`. So a Ramanujan-type bound is precisely what excludes
  Davenport–Heilbronn, and Selberg's class `S` imposes it as an axiom.
- **torsion** of the roots on top of Ramanujan — the Euler product itself.

So the correct slogan is not "multiplicativity is discreteness" but:

> **multiplicativity = Ramanujan + torsion, read off the root locus of the virtual local
> polynomial `N_p`.**

Both tiers are discontinuous in the coefficients; only the second is invisible to every norm. This
is a sharper answer to `euler-defect-controls-displacement.md` than §7 gave, and it is stable under
the attack that killed §7.

### 10.4 What this opens

Within the **Selberg class** `S` (Ramanujan imposed) the local roots satisfy `|r| >= 1`
automatically, so Theorem 6 collapses: case 2 cannot occur, and `B_p` is discrete **iff** it is
finite **iff** `N_p` is cyclotomic. Hence:

> **[COROLLARY, conditional on the open core]** Inside the degree-one Selberg class with the
> Ramanujan axiom, discreteness of `{b_n}` is equivalent to the Euler product.

That is a clean statement whose only missing input is the open core, and it explains structurally why
Selberg had to put Ramanujan and the Euler product in as separate axioms: they are the two tiers of
one root-locus condition, and the first does not imply the second.

## Log (cont.)

- 2026-07-25 (cycle 2) — two-prime rational generating function; slice poles; local torsion
  propagates; composite coefficients carry no extra slice information.
- 2026-07-25 (cycle 3) — level error in §7 found and corrected (discrete ≠ finite); Theorem 6
  trichotomy; Davenport–Heilbronn exhibited as a counterexample to §7, answering the parent card's
  open finite task; invariant repaired to Ramanujan + torsion; Selberg-class corollary stated.

---

## 11. The tool for the open core: local polynomials evaluate to character coefficients

Let the modulus `Q` be prime, `m = Q - 1`, `g` a primitive root, `omega = e^{2 pi i/m}`, and write
`v_i = alpha(g^i)`, `v_0 = 1`. Expand `alpha` on `(Z/Q)^×` in multiplicative characters,
`alpha = sum_chi c_chi chi`, and index them by `chi_l(g) = omega^l`, so `v_i = sum_l c_{chi_l}
omega^{il}`.

For `j` coprime to `m` put `N^{(j)}(X) = sum_{i<m} v_{ij mod m} X^i` — the virtual local polynomial
at any prime `p ≡ g^j`. Evaluating at an `m`-th root of unity and reindexing `i' = ij`:

  **`N^{(j)}(omega^{-t}) = sum_i v_{ij} omega^{-it} = sum_{i'} v_{i'} omega^{-i' j^{-1} t}
   = m · c_{chi_{j^{-1} t}}`.**  `[PROVED HERE]`

So *the values of every virtual local polynomial at the `m`-th roots of unity are the multiplicative
Fourier coefficients of `alpha`, permuted by the multiplicative group `(Z/m)^×`.*

Consequences, immediately:

- `N^{(j)}` vanishes at `omega^{-t}` exactly when `c_{chi_{j^{-1}t}} = 0`. Hence **every** `N^{(j)}`
  has exactly `m - S` roots among the `m`-th roots of unity, where `S = #{chi : c_chi ≠ 0}`.
- `alpha|(Z/Q)^×` is a Dirichlet character **iff** `S = 1` (and then the nonzero coefficient is `1`).
- If `alpha` never vanishes on units then `deg N^{(j)} = m - 1` for every `j`, so `N^{(j)}` has
  exactly `S - 1` roots that are roots of unity of order **not** dividing `m`.

The open core is therefore the following completely finite statement:

> **[OPEN CORE, character-coefficient form]** Let `c : hat{(Z/Q)^×} → C` with `sum_chi c_chi = 1`,
> and let `alpha = sum c_chi chi` be an eigenvector of the additive DFT on `Z/Q` (equivalently
> `c_{chi-bar} tau(chi-bar)/sqrt{Q} = eps c_chi` for all `chi`). If for every `j` coprime to `m` the
> degree `< m` interpolation polynomial taking the value `m c_{chi_{j^{-1}t}}` at `omega^{-t}` has
> **all** its roots roots of unity, then `S = 1`.

Davenport–Heilbronn is the case `S = 2` with `S - 1 = 1` extra root, and that root is `∓1/xi`, which
by §10.2 is exactly not a root of unity. Proving that `S >= 2` always produces a non-torsion extra
root would close the core. The Gauss-sum relation is what ties the `c_chi` together across the
permutation action, and §6's modulus-3 computation is the smallest instance of the two constraints —
torsion of the extra roots, and the eigenvector relation — being incompatible.

---

## 12. NOVELTY RETRACTION (external gate)

Re-judged against the **external literature**, not against corpus absence.

Theorems 1–6 of this card are a generating-function computation for the logarithmic derivative of a
Dirichlet series with periodic coefficients, plus the standard root-locus reading of the Selberg
class axioms. The ingredients — Kaczorowski–Perelli's degree-one structure theorem, Saias–Weingartner,
the local Ramanujan condition, Kronecker's theorem on roots of unity — are all classical, and a
specialist in the Selberg class would produce the local formula on demand. The Davenport–Heilbronn
computation is a two-line Gauss-sum evaluation inside a fully worked classical example.

**Verdict: `[REDISCOVERED / INSIGNIFICANT]`.** The frontier as the literature states it is not
moved. The card is retained only as a worked local dictionary; it is *not* new scientific knowledge
and must not be counted as such.

**Procedural cause, named.** The card was built on the "Steering" paragraph of
`euler-defect-controls-displacement.md` — a card the corpus had **already downgraded to
`[REDISCOVERED]` in its own final section**. Taking a retired card's forward-pointer as a live lead
is the error. A lead is live only if it comes from what the corpus *proves*, read as a whole.
