# Infinite-prime Wold--Higgs energy purity

- **ID:** `infinite-prime-wold-higgs-energy-purity`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper bridge) / SOURCE-EFFECTIVITY CONJECTURE
- **Scientific status:** `[EXACT SELECTOR PAPER-PROVED]`
  `[HARDER--NARASIMHAN SHORTCUT FALSIFIED]`
  `[SOURCE TRANSFER OPEN] [NOT RH]`
- **Parents:**
  - `global-wold-volume-gamma-bimoderate-completion.md`;
  - `source-curved-prime-torus-conormal-temperedness.md`;
  - `deninger-enhanced-adiabatic-milnor-calderon-vanishing-cycle.md`;
  - `deninger-tate-poisson-pro-hodge-rigging.md`;
  - `unit-exponential-wold-calderon-suspension.md`.
- **RH used:** no.
- **Computation used:** no.
- **Statement:** Every finite prime packet admits a harmonic rank-one system with arbitrary
  centered real slope, but the source-forced Wold energy of the coherent power character is
  cofinally finite only at slope zero.  The missing RH theorem is not ordinary polystability; it is
  source-effective conservation of every Xi conormal fibre into this infinite-prime finite-energy
  harmonic limit.

## Goal

Turn the instruction “we need infinity” into an exact discriminator.  Finite prime tori cannot
force unitarity: every rank-one character is semisimple and has a harmonic metric.  The ordinary
all-prime Hilbert regular representation also cannot force RH because it erases point fibres.

The candidate third completion instead keeps the point character as a rank-one local system and
completes only its **nonunitary Higgs displacement** in the source-forced Wold energy.  This is
Hausdorff, retains every unitary point character, admits localized square-summable nonunitarity,
but rejects every globally coherent off-line power character.

## 1. Finite prime harmonic character

For a finite prime set \(P\), put
\[
 G_P=\bigoplus_{p\in P}\mathbb Z,\qquad
 \widehat G_P=(S^1)^P.
\]
For \(s\in\mathbb C\), the centered conormal character is
\[
 \lambda_p(s)=p^{1/2-s},\qquad
 \chi_{P,s}(e)=\prod_{p\in P}\lambda_p(s)^{e_p}.          \tag{1}
\]
Write
\[
 \alpha=\Re s-\frac12.
\]
The polar decomposition of the \(p\)-holonomy is
\[
 \lambda_p(s)
 =p^{-i\Im s}\,p^{-\alpha}.                              \tag{2}
\]
The first factor is unitary.  The logarithm of the positive factor,
\[
 a_p(s)=\log|\lambda_p(s)|=-\alpha\log p,                \tag{3}
\]
is the real rank-one Higgs displacement in the abelian nonabelian-Hodge decomposition.  Every
finite packet has finite energy for every \(s\); no finite-dimensional Hodge or stability theorem
can select \(\alpha=0\).

### Transverse-orbit typing `[PROVED HERE]`

This character circle is not a new copy of \(S^1\).  Deninger's transverse prime orbit is
\[
 S_p=\mathbb R/(\log p)\mathbb Z
\]
with Fourier basis
\[
 t\longmapsto \exp(2\pi i e t/\log p),\qquad e\in\mathbb Z.
\]
Thus its Fourier lattice is literally the prime-valuation lattice used in `(1)`.  The normalized
coordinate
\[
 \theta_p={2\pi t\over\log p}
\]
identifies its Pontryagin dual with the prime-angle circle, preserving the valuation orientation.
Moreover the flat connection
\[
 \nabla_{p,s}=d+(s-\tfrac12)\,dt                         \tag{3a}
\]
has holonomy
\[
 \exp\bigl(-(s-\tfrac12)\log p\bigr)=p^{1/2-s}.          \tag{3b}
\]
Changing the orbit origin conjugates a chosen point-coordinate but changes neither `(3b)` nor its
energy.  This closes the former ambiguity between the Deninger transverse orbit and the conormal
prime-angle character.  It does not identify either with a leafwise Kummer circle.

## 2. Tate energy and its Wold-equivalent refinement

The proved Deninger packet topology supplies the Tate weight
\[
 \beta_p=(\log p)^2.                                     \tag{4}
\]
For a rank-one character, the normalized harmonic calculation below turns this into the finite
Tate--Higgs energy
\[
 \mathcal E_P^{\mathrm{Tate}}(\chi)
 =\sum_{p\in P}\bigl(\log|\chi(p)|\bigr)^2.              \tag{5}
\]

Independently, the adjacent BV/Wold/Calderón theorem supplies the literal prime-cell mass
\[
 \delta_p=1-p^{-1}.                                      \tag{5a}
\]
It is simultaneously the off-\(p\)-multiple Laurent residue fraction, multiplication-Wold defect
density, and unit-exponential Calderón first-cell mass.  If the two source directions are coupled
by their product measure, the corresponding refinement is
\[
 \mathcal E_P^{W}(\chi)
 =\sum_{p\in P}\delta_p\bigl(\log|\chi(p)|\bigr)^2.       \tag{5c}
\]
The source-relative product coupling itself is not yet proved.  However it cannot change the
completion: for every prime,
\[
 {1\over2}\leq\delta_p<1,
\]
so
\[
 {1\over2}\mathcal E_P^{\mathrm{Tate}}
 \leq\mathcal E_P^W
 \leq\mathcal E_P^{\mathrm{Tate}}.                       \tag{5b}
\]
Thus the already-proved Tate normalization and the proposed Wold-refined energy define the same
Hausdorff finite-energy character space.  No zero, divisor norm, or fitted decay weight enters
either topology.

For the coherent power character `(1)`,
\[
\boxed{\;
 \mathcal E_P^W(s)
 =\alpha^2\sum_{p\in P}(1-p^{-1})(\log p)^2.
\;}                                                     \tag{6}
\]

### Exact local Dirichlet derivation `[PROVED HERE]`

Let \(x_p:\mathbb R\to\mathbb R\) be the real harmonic-metric coordinate of a rank-one
local system with holonomy \(\lambda_p\).  It satisfies
\[
 x_p(t+\log p)=x_p(t)+\log|\lambda_p|.                   \tag{6b}
\]
Among all such equivariant \(H^1_{\rm loc}\) maps, Cauchy--Schwarz gives the sharp normalized
Dirichlet bound
\[
 \int_{0}^{\log p}|x_p'(t)|^2\,{dt\over\log p}
 \geq{\bigl(\log|\lambda_p|\bigr)^2\over(\log p)^2},     \tag{6c}
\]
with equality exactly for the affine harmonic map.  Multiplication by the forced Tate weight
`(4)` gives the unconditional identity
\[
 \beta_p
 \min_{x_p\ {\rm satisfying}\ (6b)}
 \int_{0}^{\log p}|x_p'|^2\,{dt\over\log p}
 =
 \bigl(\log|\lambda_p|\bigr)^2.                          \tag{6d}
\]
If the independent Wold first-cell direction is coupled by its product mass `(5a)`, `(6d)` becomes
\[
 \delta_p\beta_p
 \min_{x_p\ {\rm satisfying}\ (6b)}
 \int_{0}^{\log p}|x_p'|^2\,{dt\over\log p}
 =
 \delta_p\bigl(\log|\lambda_p|\bigr)^2.                  \tag{6e}
\]
Therefore `(5)` is not a guessed diagonal norm: it is the minimal transverse harmonic energy
forced by Deninger's Tate normalization.  Equation `(6e)` is the only compatible product-weight
refinement using the exact Wold/BV/Calderón cell mass, but constructing that product at chain level
remains open.  By `(5b)` this coupling affects the source interpretation, not the finite-energy
selector.

## 3. Infinite-prime energy-purity theorem `[PROVED HERE]`

Let \(P\) run cofinally through the finite prime sets.  For either energy in Section 2,
\[
 \sup_P\mathcal E_P^{\mathrm{Tate}}(s)<\infty
\quad\Longleftrightarrow\quad
\sup_P\mathcal E_P^W(s)<\infty
 \quad\Longleftrightarrow\quad
 \alpha=0
 \quad\Longleftrightarrow\quad
 \Re s=\frac12.                                         \tag{7}
\]
Indeed, if \(\alpha=0\), every term in `(6)` is zero.  If \(\alpha\ne0\), then for every prime
\[
 (1-p^{-1})(\log p)^2
 \geq \frac12(\log2)^2.
\]
The sum over any cofinal sequence of finite prime sets therefore diverges.  No prime number theorem
or zero information is required.

This is stronger than a one-prime moderation screen in one respect and weaker in another:

- it is genuinely an infinity theorem; every finite packet permits \(\alpha\ne0\);
- it allows arbitrary localized nonunitarity
  \((\log|\chi(p)|)_p\in\ell^2(\delta)\), while excluding the coherent arithmetic ray
  \((-\alpha\log p)_p\) unless \(\alpha=0\).

Multiplicity jets do not change `(7)`: they enlarge the nilpotent/generalized fibre but retain the
same semisimple holonomy and hence the same real Higgs displacement `(3)`.

## 4. Concrete third character completion

Define
\[
 \operatorname{Char}_{W}(G)
 =
 \left\{
  \chi:G\to\mathbb C^\times:
  \sum_p(\log|\chi(p)|)^2<\infty
 \right\}.                                               \tag{8}
\]
Polar decomposition identifies `(8)` with
\[
 \widehat G\times\ell^2(\{\text{primes}\},\delta_p;\mathbb R)                 \tag{9}
\]
as a Hausdorff topological group.  Thus:

1. every unitary prime character remains an actual point fibre;
2. the nonunitary tangent is a complete Hilbert space;
3. finite prime restriction is continuous and surjective;
4. the coherent power-character curve meets `(8)` exactly on the critical line.

This is not a Hilbert space of scalar functions on \(\widehat G\), so it does not erase point
fibres into continuous spectrum.  It is also not the full hyperfunction character space, so it does
not admit arbitrary exponentially displaced coherent rays.

## 5. Why ordinary polystability is a false shortcut

A tempting claim is:

```text
product formula gives total slope zero
  + source object is polystable
  -> every Xi constituent has slope zero.
```

That claim is false in the relevant rank-one nonabelian-Hodge category.  A rank-one complex local
system is always semisimple and therefore admits a harmonic metric.  Its corresponding Higgs line
bundle is stable of degree zero even when its monodromy is nonunitary.  Nonunitarity is stored in
the nonzero Higgs field, not in the Harder--Narasimhan slope.  Hence ordinary semistability or
polystability cannot imply `(7)`.

There is a second scalar no-go.  The meromorphic connection
\[
 d+d\log\Xi
\]
is gauge-equivalent to the trivial connection away from the divisor, and its integer residues have
trivial exponential monodromy.  It detects divisor support and total multiplicity but does not
encode horizontal prime-character displacement.  Applying wild-harmonic or pure-twistor machinery
to this scalar connection alone cannot prove RH.

There is a third, corpus-specific no-go.  The proved positive-time Deninger form
\[
 \langle f,\widehat A_p e^{-2r\widehat A_p}f\rangle
\]
is deliberately restricted to nonzero circle Fourier modes.  The real holonomy coordinate in
`(6b)` is represented by a constant harmonic \(1\)-form, not by an oscillatory boundary function.
It therefore lies outside the sector controlled by the existing Dirichlet-to-Neumann estimate.
Quoting that estimate as a bound for `(6d)` would be a type error.

```text
[NO-GO]
Ordinary HN semistability, rank-one harmonicity, or the scalar logarithmic Xi connection forces
unitary prime holonomy.  Existing oscillatory Poisson positivity does not control the missing
harmonic-H1 channel.

[POSITIVE]
The missing datum is finite energy of the transverse nonunitary Higgs field across infinitely many
source-labelled prime circles, carried by an added harmonic-H1 channel and compatibly refined by
the exact Wold masses `(5a)`.
```

This correction is load-bearing.  Simpson's correspondence explicitly makes semistability of flat
bundles vacuous, while Mochizuki's wild correspondence identifies good wild harmonic bundles with
polystable filtered flat objects; neither theorem supplies the arithmetic cofinal energy `(5)`.

## 6. Frozen source theorem

> **[CONJECTURE -- SOURCE-EFFECTIVE WOLD--HIGGS FINITE-ENERGY TRANSFER.]**
> Form the strict all-prime enhanced Euler--Gamma/Calderón object before divisor specialization.
> Its moderate harmonic boundary admits a source-defined transverse rank-one realization
> \[
>  \mathcal R_W:
>  N_\Xi^{\mathrm{src}}\longrightarrow\operatorname{Char}_W(G)
> \]
> satisfying:
>
> 1. the \(p\)-holonomy of a conormal fibre at \(\rho\) is the already-proved centered character
>    \(p^{1/2-\rho}\);
> 2. the local harmonic energy is the Tate-normalized orbit energy `(6d)`, and its relative
>    Wold/BV/Calderón realization is the product refinement `(6e)`;
> 3. every principal Xi conormal and every multiplicity jet has a nonzero finite-energy image;
> 4. the construction is made from the positive prime-power source, Gamma/real transgression,
>    strict aperture-Stokes transport, and source orientation before a zero is selected;
> 5. equivalent prime exhaustions act by the exact annular Stokes cocycle and preserve the
>    finite-energy graph class.

If this theorem holds, `(7)` applies to every nontrivial zero \(\rho\) and proves RH.

Clause 3 is the load-bearing source theorem.  Once the character law in clause 1 is fixed, its
finite-energy assertion is RH-equivalent.  It may not be assumed as a definition of the target
topology or proved by expanding the Xi divisor and deleting infinite-energy fibres.

## 7. Concrete attack

1. Construct the missing harmonic-\(H^1\) holonomy channel alongside the proved all-prime Deninger
   Poisson form.  The existing Dirichlet-to-Neumann form acts only on nonzero Fourier modes and
   does not see the constant harmonic \(1\)-form carrying `(6b)`.
2. Construct the source-relative product with the Wold cell and recover `(6e)` at chain level.
3. Transport the exact local energy graph `(6b)`--`(6e)`, not only its scalar trace, through the exact annular
   Schur/Pick cocycle and Gamma/Calderón continuation.
4. Prove a boundary-energy estimate uniform under the source-curved approach to \(h=0\) after the
   already-forced Mertens/first-trace counterterm.
5. Identify the nonzero residues of the limiting Green connection with all principal conormal
   jets and prove that the comparison is strict.

Step 1 is the first non-immediate analytic obstacle.  Finite packet harmonicity, ordinary
polystability, and scalar determinant convergence do not address it.

## 8. Hostile falsifiers

Retire the mechanism if any of the following occurs.

1. The Deninger transverse circle and the conormal prime-angle circle cannot be compared by a
   source-defined map.
2. The local Green/Higgs energy is not \(\delta_p(\log|\chi(p)|)^2\) up to one universal scalar.
3. Gamma/Calderón continuation controls only a scalar determinant and not the cofinal energy graph.
4. The \(h=0\) counterterm which makes the energy finite depends on \(\rho\), its real part, or a
   divisor-selected norm.
5. One Xi multiplicity jet disappears in the finite-energy boundary.
6. An explicit off-line generalized-prime Euler system carries the same literal integer
   multiplication Wold cells, adjacent BV residue maps, Gamma transgression, and strict
   finite-energy conormal comparison.
7. The only proof of clause 3 is that non-finite-energy fibres are declared zero.
8. The proposed proof silently applies the oscillatory Dirichlet-to-Neumann form to the constant
   harmonic \(1\)-form carrying nonunitary holonomy.

The strongest positive survivor after failure would be an exact classification of which
source-defined conormal sectors have square-summable nonunitary Higgs displacement.

## 9. Literature boundary

Parent theory:

- Simpson's harmonic-bundle correspondence: semisimple flat bundles correspond to harmonic
  bundles, and polystable Higgs bundles to Hermitian--Yang--Mills metrics;
- Corlette's canonical harmonic metrics for reductive flat bundles;
- Sabbah--Mochizuki wild harmonic bundles and polarized twistor \(D\)-modules;
- rank-one twistor deformation and the decomposition of a character into unitary and real-Higgs
  parts;
- elementary weighted \(\ell^2\) character completions.

Primary references:

- Carlos Simpson, *Higgs bundles and local systems*,
  <https://archive.numdam.org/item/PMIHES_1992__75__5_0/>;
- Takuro Mochizuki, *Wild Harmonic Bundles and Wild Pure Twistor D-modules*,
  <https://arxiv.org/abs/0803.1344>;
- Takuro Mochizuki, *Good Wild Harmonic Bundles and Good Filtered Higgs Bundles*,
  <https://arxiv.org/abs/1902.08298>;
- Morihiko Saito, *Twistor deformation of rank one local systems*,
  <https://arxiv.org/abs/1307.4907>.

Targeted searches found no construction coupling those parent correspondences to the exact
integer-multiplication Wold masses, the BV adjacent conormal fraction, and the strict all-prime Xi
source boundary.  Search noncollision is not a priority certificate.  The theorem `(7)` is an
elementary bridge, not a novelty claim.  Candidate-new mathematics begins only with the
source-effective comparison in Section 6 and its uniform boundary-energy theorem.

## Gates

- [x] derive the exact finite-packet Wold--Higgs energy
- [x] prove the cofinal energy-purity theorem
- [x] construct the Hausdorff finite-energy character completion
- [x] falsify ordinary HN/polystability as a unitarity mechanism
- [x] falsify the scalar \(d\log\Xi\) connection as a horizontal-slope carrier
- [x] run initial corpus and external parent audits
- [x] identify the Deninger transverse circle with the conormal prime-angle circle
- [x] derive the exact local Tate harmonic energy and prove Wold norm equivalence
- [ ] construct the harmonic-\(H^1\) holonomy channel in the source complex
- [ ] construct the chain-level Wold product coupling
- [ ] prove uniform renormalized boundary energy through Gamma/Calderón continuation
- [ ] prove strict all-prime principal-conormal and multiplicity-jet conservation
- [ ] obtain a dependency-closed source theorem
- [ ] formalize only after the source theorem is paper-proved
- [ ] derive unconditional RH

## Log

- 2026-07-29 — Generated the infinite-prime finite-energy mechanism after the ordinary
  Harder--Narasimhan idea failed: nonunitary rank-one systems remain harmonic and stable at every
  finite stage.  The positive survivor is cofinal Wold energy of the real Higgs displacement,
  which diverges on every coherent off-line power character while retaining all unitary point
  fibres.
- 2026-07-29 — Closed two typed bridges on paper.  Deninger's orbit
  `R/(log p)Z` has the valuation Fourier lattice and the centered connection has holonomy
  `p^(1/2-s)`.  The minimal equivariant harmonic energy, multiplied by the already-forced Tate
  weight `(log p)^2` and Wold cell mass `1-p^-1`, is exactly
  `(1-p^-1)(log|p^(1/2-s)|)^2`.
