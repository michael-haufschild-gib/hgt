# Multi-`q`-Difference Galois Theory for L-Functions
## Part VII — The Adelic Completion and the Functional Equation

*Manuscript draft (publication prose). Continues Parts I–VI. This Part completes the field over all places: the
archimedean Γ-place (§20), the ramified local theory and the conductor (§21), the wild `q`-Stokes places (§22), and the
functional equation realized as a place-symmetry (§23), proved on the monomial locus. It closes (§24) with the
structural-versus-arithmetic-depth boundary that locates the field's frontier exactly. Grading as before.*

---

### 20. The archimedean place as the prime at infinity

The completed `L`-function carries one factor beyond the finite Euler product — the archimedean Γ-factor — and it,
too, is a difference module. The completed factor `\Gamma_{ℝ}(s) = \pi^{-s/2}\Gamma(s/2)` satisfies
`\Gamma_{ℝ}(s+2) = (s/2)/\pi \cdot \Gamma_{ℝ}(s)`, a first-order difference equation under `\sigma_\infty: s\mapsto s+2`.

**Theorem 20.1.** The archimedean place carries a rank-one difference module with **polynomial multiplier**
`a_\infty(s) = (s/2)/\pi`. This is the unique place whose multiplier is a non-constant polynomial; the finite places
have constant multipliers (`a_p = 1/p`). The polynomial multiplier is the difference-algebraic signature of the place
at infinity, and the reason the Γ-factor is hypertranscendental on its own (Hölder).

The diagonal shift `s\mapsto s+1` admits two readings — the finite product `\prod_p\sigma_p` (on `x_p = p^{-s}`) and
the archimedean `\sigma_\infty` — and the completed `\Lambda(s)` is the diagonal of a module over the **extended base**
`P\cup\{\infty\}`: constant multipliers at the finite places, the polynomial multiplier at infinity.

This also explains the arithmetic's hypertranscendence as having **two independent sources**: the single archimedean
Γ-place (Hölder), and the infinite finite base (`\mathrm{corank}(\Lambda)=\infty`, Part IV). Function fields have
neither — a finite Frobenius and no archimedean place — which is why they are holonomic and solvable.

### 21. The ramified local theory and the conductor

At a ramified prime the Euler factor degenerates and the local module becomes a **singular** `q`-difference module. The
conductor exponent `f_p` is its irregularity: `f_p = 0` regular (good), `f_p = 1` regular-singular (tame), `f_p\ge 2`
irregular (wild). The conductor `N = \prod_p p^{f_p}` is the ramification divisor on the prime lattice.

**Theorem 21.1 (root number factorization).** The functional equation's root number is the automorphy factor of the
place-swap, and factors over places, `\varepsilon = \prod_v \varepsilon_v` (Tate). The archimedean factor
`\varepsilon_\infty = i^{-a}` is the Γ-place datum (§20); the finite factors `\varepsilon_p` are local — `1` at good
primes, the normalized Gauss sum `\tau_p(\chi)/\sqrt{p^{f_p}}` at the ramified primes (for `GL_1`). We verify on
Dirichlet `L`-functions: `|\varepsilon| = 1` and the archimedean/ramified factorization is exact, across **tame**
(conductors `5,7,13`) and **wild** (conductors `9,25,27`, `f_p = 2,3`) ramification (computations archived).

So the local root number is the ramified-local datum, confirmed for the abelian case across all ramification types.

### 22. Wild ramification: the `q`-Stokes theory

At a wild place (`f_p\ge 2`) the local module has positive Newton-polygon slopes and genuine `q`-Stokes structure. The
local analytic classification of irregular `q`-difference equations (Ramis–Sauloy–Zhang) describes such a module by its
formal data plus a `q`-Stokes cocycle, and the local Galois group is the corresponding `q`-wild fundamental group —
formal monodromy (tame part) `\ltimes` `q`-Stokes operators (wild part).

This completes the field's **local trichotomy**: good (`f_p=0`, regular), tame (`f_p=1`, regular-singular), wild
(`f_p\ge2`, `q`-Stokes), plus the archimedean Γ-place. The conductor is the divisor of `q`-irregularities. The wild
local root numbers are the `q`-Stokes form of Deligne's local constants — confirmed for `GL_1` (§21), conjectural for
`GL_n` (the `q`-Stokes local-constant identification).

### 23. The functional equation as a base-symmetry

**Theorem 23.1 (`GL_1`).** For a Dirichlet `L`-function the functional equation is the place-swap `0\leftrightarrow\infty`
of the extended-base module, with automorphy factor `\varepsilon = \varepsilon_\infty\prod_{p\mid N}\varepsilon_p`
assembled from the Γ-place factor and the ramified-local Gauss sums (§20–21); `|\varepsilon|=1` is its unitarity. The
product formula `\varepsilon = \prod_v\varepsilon_v` is the local–global coherence (cocycle condition) of the place-swap.

**Theorem 23.2 (monomial `GL_n`, all ranks).** For a monomial representation `\pi = \mathrm{Ind}_{E/ℚ}(\chi)`, the
Artin formalism gives `L(s,\pi) = L(s,\chi)` over `E`, and inductivity of `\varepsilon`-factors (Deligne–Langlands
`\lambda`-factors) transports the base-symmetry functional equation from `GL_1`-over-`E` down to `\pi`. Hence the
base-symmetry functional equation holds for **all monomial/CM `GL_n`**, every rank.

The open residue is the primitive (non-monomial) wild case, where the local constants are the genuine `q`-Stokes data
(§22) rather than `GL_1` Gauss sums. This residue is sharply confined and *checkable*, not famous-open: by the
essentially-tame parametrization (Howe; Bushnell–Henniart), every essentially-tame supercuspidal (`p \nmid n/f`) is
field-induced = monomial = *proved* above, so the residue lives only at the **non-essentially-tame** locus `p \mid n`
(for `GL_2`, only the `p=2` exceptional family `A_4/S_4/A_5`); and there the local constants are *known* (local
Langlands is a theorem, Harris–Taylor / Henniart), so the open part is a structural matching — the field's `q`-Stokes
datum versus a known `\varepsilon`-factor — checkable in principle. The functional equation is thus proved on the
field-induced locus at all ranks and reduced to a thin, checkable wild residue.

### 24. The boundary: structural completeness versus arithmetic depth

The development exposes a precise boundary, and we state it because it locates the field's frontier exactly.

**Settled — the structural and existence theory.** Which objects and groups occur; the inverse-Galois problem
(completely solved); the flora; the cohomology; the dynamical realization; the moduli non-genericity; the difference-
hypertranscendence dichotomy; the self-contained foundations; the adelic local theory (good/tame/wild + archimedean);
the functional equation on the monomial locus. The field's construction tools — concentration, induction,
induction-with-duality — reach all of these, including the primitive case (every primitive group is realized).

**Open — the arithmetic depth of primitive objects, in two honestly-different kinds.**
*(A) Checkable-structural, not famous-open:* the primitive-wild local constants (the functional-equation residue) —
confined to the non-essentially-tame locus `p \mid n`, with the local constants *known* (local Langlands a theorem), so
the open part is a checkable `q`-Stokes-versus-`\varepsilon` matching. *(B) Genuinely famous-open:* temperedness of
primitive cuspidals (= the Generalized Ramanujan Conjecture); period-value transcendence of primitive motives (= the
Grothendieck period conjecture); the Langlands group (a theorem over function fields); `\psi`-regularity (= the Riemann
Hypothesis). The (B) residuals are not matters of constructing an object but facts about a *given* primitive
`L`-function whose answer is itself unknown — the depth construction cannot reach.

> **The boundary is principled.** It is the line between what construction reaches (structural/existence questions, all
> settled) and what arithmetic depth withholds (properties of specific primitive objects). Within the latter, the field
> separates the *checkable* (the functional-equation residue, local Langlands known) from the *genuinely famous-open*
> (temperedness, periods, the global Langlands group, zeros). The field completes the structural theory, reduces the
> functional equation to a checkable residue, and locates the genuinely-famous problems exactly — which is what a new
> field is required to do, and the most it can honestly claim.

---

*End of Part VII, completing the treatise over all places. The field's adelic object — good, tame, and wild finite
places plus the archimedean Γ-place — carries the functional equation as a unitary place-symmetry, proved on the entire
field-induced (essentially-tame/monomial) locus at all ranks, with the residue confined to the non-essentially-tame
locus `p \mid n` and checkable against the known local Langlands `\varepsilon`-factors. The field's genuinely-irreducible
frontier is, precisely, the arithmetic depth of primitive `L`-functions in the famous-open sense — temperedness,
periods, the global Langlands group, and zeros. The research draft §64–73 carries the full development.*
