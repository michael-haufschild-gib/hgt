# Reciprocal Hadamard mixed-cumulant reconstruction and global properness law

- **ID:** ULF-BFIM-1
- **Stage:** 3-formalized
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ConstitutiveBiFormationInterference`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveBiFormationAllOrder`,
  `GaloisForLFunctions.HTGeometry.GaussianQuadraticCumulantCharacterization`
- **Type:** THREE-ORGAN FUSION + FOURTH-ORGAN PREDICTION + GLOBAL FORMATION THEOREM
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL]`
  `[INDEPENDENT-FORMATION ADDITIVITY] [RECIPROCAL POLARIZATION]`
  `[COMPLETE CUMULANT RECONSTRUCTION] [RENORMALIZED CHARGE CONSERVATION]`
  `[CLASSICAL GAUSSIAN-CHARACTERIZATION PARENT] [LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [NOT RH]`

## 1. Two source compositions

Let `X,Y` be independent identically distributed real random variables.  Assume their moment
generating function is finite in a neighborhood of zero and write the analytic cumulant generator

\[
 K(z)=\log \mathbb E e^{zX},
 \qquad
 \kappa_r=K^{(r)}(0).
 \tag{BFI.1}
\]

For a real scale `a`, reciprocal Hadamard mixing forms

\[
 S_a=a(X+Y),
 \qquad
 D_a=a(X-Y).
 \tag{BFI.2}
\]

Independent formation and Hadamard mixing are different composition laws.  The joint cumulant
generator of `(S_a,D_a)` is

\[
 H_a(s,t)=K(a(s+t))+K(a(s-t)).
 \tag{BFI.3}
\]

Define their **interference germ** by removing both marginal generators:

\[
 \mathcal I_{K,a}(s,t)
 =H_a(s,t)-H_a(s,0)-H_a(0,t)+H_a(0,0).
 \tag{BFI.4}
\]

Since `K(0)=0`, this is explicitly

\[
 \boxed{
 \mathcal I_{K,a}(s,t)
 =K(a(s+t))+K(a(s-t))-2K(as)-K(at)-K(-at).}
 \tag{BFI.5}
\]

The two mixed channels are independent exactly when their joint cumulant generator splits, hence
exactly when `(BFI.5)` vanishes near the origin.

## 2. Complete mixed-response reconstruction

### Theorem 2.1 — response spectrum

For every integer `r>=3`,

\[
 \boxed{
 \left.
 \partial_s^{r-2}\partial_t^2\mathcal I_{K,a}(s,t)
 \right|_{(0,0)}
 =2a^r\kappa_r.}
 \tag{BFI.6}
\]

Consequently, if `a!=0`, the complete mixed-response spectrum reconstructs every higher cumulant:

\[
 \boxed{
 \kappa_r={1\over 2a^r}
 \left.
 \partial_s^{r-2}\partial_t^2\mathcal I_{K,a}
 \right|_{(0,0)}.}
 \tag{BFI.7}
\]

#### Proof

Expand `K(z)=sum_(n>=1) kappa_n z^n/n!` near zero.  In `(BFI.5)`, pure powers of `s` are cancelled
by `2K(as)` and pure powers of `t` by `K(at)+K(-at)`.  The coefficient of
`s^(r-2)t^2` in

\[
 K(a(s+t))+K(a(s-t))
\]

is

\[
 {\kappa_r a^r\over r!}
 \left(\binom r2+\binom r2\right).
\]

Multiplication by `(r-2)!2!` when taking the mixed derivative gives

\[
 {\kappa_r a^r\over r!}\,2\binom r2\,(r-2)!2!
 =2a^r\kappa_r.
\]

This proves both formulas. ∎

### Theorem 2.2 — flat-sector classification

For `a!=0`, the following are equivalent:

1. `I_(K,a)=0` on a neighborhood of `(0,0)`;
2. every higher cumulant `kappa_r`, `r>=3`, vanishes;
3. `K(z)=kappa_1 z + kappa_2 z^2/2` near zero;
4. `X` is Gaussian, allowing the degenerate variance-zero case.

#### Proof

Theorem 2.1 gives `1=>2`.  Analyticity gives `2=>3`.  Direct substitution proves `3=>1` by the
parallelogram identity.  Finally, an analytic moment generating function determines the law;
the exponential of the quadratic cumulant generator is the Gaussian moment generating function.
Thus `3<=>4`. ∎

This is the fourth-organ prediction: complete interchange flatness is not a new arbitrary notion of
positivity.  It forces the classical quadratic/Gaussian chamber.

## 3. Exact finite third-current identity

The first current needs no analytic moment-generating function.

Let `I` be finite, let real weights `(w_i)` satisfy `sum_i w_i=1`, and let real centered values
`x_i` satisfy `sum_i w_i x_i=0`.  Put

\[
 \kappa_3=\sum_iw_i x_i^3.
 \tag{BFI.8}
\]

Draw two independent indices `(i,j)` with product weight `w_iw_j` and define

\[
 S_a(i,j)=a(x_i+x_j),
 \qquad
 D_a(i,j)=a(x_i-x_j).
 \tag{BFI.9}
\]

### Theorem 3.1 — oriented mixed third current

\[
 \boxed{
 \sum_{i,j}w_iw_jS_a(i,j)D_a(i,j)^2
 =2a^3\kappa_3.}
 \tag{BFI.10}
\]

#### Proof

The pointwise identity is

\[
 (x_i+x_j)(x_i-x_j)^2
 =x_i^3+x_j^3-x_i^2x_j-x_ix_j^2.
\]

After summing with product weights, the first two terms give

\[
 2\left(\sum_iw_ix_i^3\right)\left(\sum_jw_j\right)=2\kappa_3,
\]

and the two mixed terms vanish because each contains `sum_i w_i x_i=0`.  Scaling supplies `a^3`.
∎

### Corollary 3.2 — exact neutral locus

If `kappa_3!=0`, the mixed third current vanishes exactly when `a=0`.  Its sign is the sign of
`a*kappa_3`; its square is nonnegative and erases the sign of `a`.

Thus reciprocal reflection `a->-a` flips the oriented cubic current but fixes its positive square.
This is the precise phase/coorientation quotient in the theorem.

## 4. Independent-formation conservation

Let `K,L` be two analytic cumulant generators.  Independent formation has cumulant generator
`K+L`.  Formula `(BFI.5)` immediately gives

\[
 \boxed{
 \mathcal I_{K+L,a}=\mathcal I_{K,a}+\mathcal I_{L,a}.}
 \tag{BFI.11}
\]

For `m` independent copies of one law, write `K_m=mK`.  Then

\[
 \boxed{
 \mathcal I_{K_m,a}=m\mathcal I_{K,a},
 \qquad
 R_r(m,a):=partial_s^{r-2}\partial_t^2\mathcal I_{K_m,a}(0,0)
 =2ma^r\kappa_r.}
 \tag{BFI.12}
\]

Hence

\[
 R_r(m+n,a)=R_r(m,a)+R_r(n,a),
 \qquad
 R_r(m,-a)=(-1)^rR_r(m,a).
 \tag{BFI.13}
\]

This is the conservation law: independent depth adds the same generated interference current.

### Theorem 4.1 — fixed-scale formation properness

Assume some `kappa_r!=0` for `r>=3`.  Then

\[
 \boxed{
 \left(\exists C<\infty\ \forall m,\ |R_r(m,a)|\le C\right)
 \Longleftrightarrow a=0.}
 \tag{BFI.14}
\]

#### Proof

At `a=0`, every response is zero.  If `a!=0`, then

\[
 |R_r(m,a)|=m\,|2a^r\kappa_r|
\]

has a strictly positive slope and is unbounded. ∎

This theorem is not invariant under a depth-dependent rescaling of `a`.  The exact invariant is the
following renormalized charge.

### Theorem 4.2 — mean- and variance-normalized conservation

For every `r>=3` and every positive integer `m`,

\[
 \boxed{m^{r-1}R_r(m,a/m)=R_r(1,a)}
 \tag{BFI.14a}
\]

and

\[
 \boxed{m^{r-2}R_r(m^2,a/m)=R_r(1,a).}
 \tag{BFI.14b}
\]

#### Proof

Substitute `(BFI.12)`:

\[
 m^{r-1}\,2m(a/m)^r\kappa_r=2a^r\kappa_r
\]

and

\[
 m^{r-2}\,2m^2(a/m)^r\kappa_r=2a^r\kappa_r.
\]

Thus variance-normalized raw response is

\[
 R_r(m^2,a/m)=m^{2-r}R_r(1,a),
 \tag{BFI.14c}
\]

which is bounded and tends to zero for every `a`, not only `a=0`. ∎

This is a sharp no-go to using bounded normalized response as a selector.  Normalization transports
the information into the conserved homogeneous charge; it does not erase it.

The same observer can therefore be periodic under reflection while its lifted formation history is
open: even responses are reflection-fixed, odd responses alternate sign, and every nonzero response
grows linearly with depth.

## 5. Positive-jump arithmetic source chamber

Suppose `X` is compound Poisson with nonzero positive jump measure `nu` on `(0,infinity)` and finite
third moment.  Its cumulant generator is

\[
 K(z)=\int(e^{zx}-1)\,d\nu(x),
\]

so

\[
 \kappa_3=\int x^3\,d\nu(x)>0.
 \tag{BFI.15}
\]

Theorem 3.1 yields the strict source current

\[
 \boxed{R_3(1,a)=2a^3\int x^3\,d\nu(x).}
 \tag{BFI.16}
\]

The abelian-zeta-gas law in ULF-FCRM-1 has exactly such a positive discrete Levy measure supported
at `k log p`.  Therefore its reciprocal Hadamard channels are dependent for every nonzero scale,
and the dependence has a source-determined coorientation.  No target divisor or RH endpoint is used
in this statement.

## 6. Split recovery and joint reconstruction

Let a common formation/recovery map encode both channels and admit a decoder returning `(S_a,D_a)`.
Evaluating `(BFI.10)` after decoding gives the same current.  Thus split recovery is
information-neutral for the interference law.  A postobserver without such a decoder may erase the
current; positivity or common formation alone does not prevent that.

This statement is module-valued, not scalar.  If `V,W` are real modules, `e:V->W` and `d:W->V`
are linear, and `d e=id_V`, then for the canonical order-`r` packet generated by `v in V`,

\[
 d\,\mathcal H_{r,a}(e v)=\mathcal H_{r,a}(v),
 \qquad
 \mathcal H_{r,a}(v)=2a^r v.
 \tag{BFI.17}
\]

More generally every linear observer commutes with packet formation.  Therefore no linear split
recovery, completion chart, matrix representation, or quotient with a retained decoder can create
or annihilate the interference charge.  Selection must occur in a nonsplit, nonlinear, or
source-exact formation law before such recovery.

More generally, a jointly separating family of decoded mixed responses reconstructs every
`kappa_r`, `r>=3`, by `(BFI.7)`.  Mean and covariance must be retained separately.  The complete
recovery packet therefore reconstructs the analytic law, while any bounded truncation can miss a
first nonzero higher cumulant.

## 7. Mechanism fusion and prediction

One formula now explains four different shadows:

| organ | theorem shadow |
|---|---|
| independent source formation | additivity `(BFI.11)` |
| reciprocal/functional-equation polarization | parity `(BFI.13)` |
| prolongation and source complexity | higher cumulants reconstructed by `(BFI.7)` |
| positive/history organ | square loses coorientation; normalized depth conserves `(BFI.14a-b)` |

The predicted fourth-organ theorem is Gaussian/quadratic flatness, Theorem 2.2.  It follows from
the interference law rather than being supplied as a Gaussian ansatz.

### 7.1 Exact carrier-valued fusion

The module law `(BFI.17)` supplies a non-scalar fusion with existing coefficient-faithful corpus
carriers.  Let `M_(S,N)` denote the finite P-G189/CCM matrix already proved in
`FrankensteinRoutePTailFluxCCMThirdJetBridge.lean`.  Its two exact descriptions are

\[
 M_{S,N}=\sum_{pe\in S}J_P(pe)\,J^{\mathrm{CCM}}_3(N)
 =\sum_{pe\in S}d(pe)\,J^{\mathrm{CCM}}_3(pe,N),
 \tag{BFI.18}
\]

where every dressing `d(pe)` is strictly positive and prime/depth labels remain present.  Taking
the real matrix module as `V` and the canonical product tensor generated by `M_(S,N)`, the
reciprocal bi-formation response is therefore

\[
 \boxed{\mathcal H_{3,a}(M_{S,N})=2a^3M_{S,N}.}
 \tag{BFI.19}
\]

This fuses three structurally different operations: independent/reciprocal source formation,
CCM's centered cubic Loewner carrier, and Route P's arithmetic tail-flux dressing.  It is more than
a scalar analogy: the complete matrix and all coefficient labels survive.

The fourth-organ prediction is functorial.  Any linear Gamma-six/Sonin transport, graph receiver,
or finite observer `T` must satisfy

\[
 T\mathcal H_{3,a}(M_{S,N})=2a^3T(M_{S,N}).
 \tag{BFI.20}
\]

If that observer belongs to a split recovery pair, decoding returns `(BFI.19)` exactly.  Thus a
split common carrier is information-neutral, while any claimed neutralization at nonzero `a` must
identify the precise nonsplit kernel or source boundary that destroys the charge.  The existing
P/CCM/Meyer--Tate/Sonin bridges provide concrete carrier and transport maps; they do **not** provide
the missing source annihilation law.  Constructing that law remains the selection gate.

## 8. Hostile boundaries

1. **Functional equation does not imply mixed-channel independence.**  Declaring
   `I_(K,a)=0` after seeing the critical line would be circular.  Selection requires a source law
   bounding, exactifying, or independently annihilating the generated current.
2. **Third order is not complete.**  Symmetric non-Gaussian laws may have `kappa_3=0`.  The complete
   response spectrum detects the first nonzero higher cumulant.
3. **Quadratic sources do not select scale.**  Gaussian laws are flat for every `a`; a nonquadratic
   source cumulant is load-bearing.
4. **Analyticity is load-bearing only for full classification.**  The finite third-current theorem
   needs only finite sums and a third moment.
5. **Arbitrary recovery can erase the current.**  Information neutrality requires a split decoder
   retaining both mixed channels.
6. **Raw properness is gauge-dependent.**  Under variance normalization the raw higher response is
   bounded and decays for every `a`; only the renormalized charge is formation-invariant.
7. **No universal HT identification.**  An infinite active cumulant tower can realize unbounded
   response rank, but hypertranscendence is not defined as cumulant nontermination.
8. **No RH claim.**  The theorem does not yet construct the pre-divisor map from a zero's radial
   displacement to the scale `a`, nor the source law controlling `(BFI.14)`.

## 9. Parent boundary

The Gaussian flat classification is the analytic cumulant proof of the classical Bernstein
sum/difference theorem and lies inside Kac--Bernstein/Skitovich--Darmois characterization theory.
See Feldman, [arXiv:1703.06484](https://arxiv.org/abs/1703.06484), and
Gavalakis--Kontoyiannis, [arXiv:2403.07209](https://arxiv.org/abs/2403.07209).  Cumulant additivity,
compound-Poisson cumulants, and duoidal/bimonoidal categories are established parents.  The result
claimed here is the exact universal-law-field coupling and its source-facing properness interface,
not novelty of those ingredients.

## 10. Lean certificate

The finite cubic core is formalized in
`GaloisForLFunctions.HTGeometry.ConstitutiveBiFormationInterference`:

1. the exact mixed-current fusion identity before normalization or centering;
2. centered third-cumulant reconstruction `(BFI.10)`;
3. reflection parity and reflection-invariance of the positive square;
4. exact neutral locus under a nonzero third cumulant;
5. additive formation-depth conservation;
6. bounded-depth properness iff neutral scale;
7. one closed capstone packaging reconstruction, coorientation loss, and global properness.

The all-order law-tensor core is formalized in
`GaloisForLFunctions.HTGeometry.ConstitutiveBiFormationAllOrder`:

1. order `k+3` cumulants are represented by arbitrary multilinear law tensors with `k+1` sum
   slots and two difference slots;
2. multilinearity derives the response `2 a^(k+3) B(1,...,1)` from the two Hadamard source legs;
3. division by the nonzero generated factor reconstructs the source cumulant diagonal;
4. reflection acts by the exact order-parity character;
5. response is additive under independent tensor formation;
6. nonzero-scale flatness of the complete response spectrum is equivalent to vanishing of the
   complete higher-cumulant tower;
7. each surviving order satisfies additive depth conservation and bounded-depth properness iff
   neutral scale.
8. mean-normalized and variance-normalized formation have exact homogeneous conserved charges,
   proving that raw boundedness is not a normalization-invariant selector.
9. the response law is valid in every real module, including vector, matrix, operator, and quotient
   carriers;
10. every linear observer commutes with canonical packet formation, and every split
    encode/decode recovery is information-neutral.

Scratch elaboration, direct leaf elaboration, and targeted builds of both leaves pass. No umbrella,
area, or project build was run. Scratch `#print axioms` audits of fusion, spectrum-flatness,
properness, and both capstones report only `propext`, `Classical.choice`, and `Quot.sound`; no new
axiom is declared. Both leaves are wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`
without building that
umbrella. Repository lint reports eleven unrelated pre-existing theorem-area ownership failures and
does not report this module.

The algebraic all-order response and formal quadratic-flatness theorem are Lean-certified.  The
analytic identification of a quadratic moment-generating germ with a Gaussian probability law —
clause 4 of Theorem 2.2 — is now certified as well, in the new leaf
`GaloisForLFunctions.HTGeometry.GaussianQuadraticCumulantCharacterization`
(`map_eq_gaussianReal_of_mgf_quadratic`, with mathlib's `mgf_gaussianReal` as the converse).

## Log

- 2026-08-18 — Bi-formation interference isolated after single-formation, exchangeability, and
  sector-selection mechanisms were shown to leave the source-formation premise untouched.
- 2026-08-18 — Finite fusion/reconstruction/properness core formalized; targeted leaf and axiom
  audits pass; umbrella import wired without an umbrella build.
- 2026-08-18 — All-order multilinear cumulant-tensor response, reconstruction, parity,
  spectrum-flatness, conservation, and properness formalized; second leaf and axiom audits pass;
  umbrella import wired without an umbrella build.
- 2026-08-18 — Module-valued naturality and split-recovery neutrality formalized; instantiated on
  the existing coefficient-faithful P-G189/CCM matrix carrier to obtain the exact `2a^3` fusion law
  and its linear fourth-observer prediction.
