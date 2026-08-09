# Static-frame incompleteness: extension, period, and topology law

- **ID:** `cfr-static-frame-incompleteness`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / THREE-AXIS NO-GO WITH POSITIVE SURVIVOR
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [CORPUS-BACKED] [NO RH] [NO LEAN WRITTEN OR BUILT]`
- **Statement:** Three route-native static shadows separately fail to determine integral period closure, first extension orientation, and cofinal Hausdorff quotient; a universal theory must provide typed reporters for all three.

## Goal

Test the strongest tempting regression after the valuated Plücker--Gram theorem:

> perhaps a sufficiently enriched static matroid frame already is the universal geometry.

Three exact countermodels reject this. The positive survivor identifies what any complete field
must retain beyond static finite dependence.

## 1. Period closure is not oriented-trivially-valuated support

Identify `C` with `R^2`. Consider the ordered triples

\[
 v=(1,i,1+i),
 \qquad
 w=(1,i,\sqrt2+i).
\tag{1}
\]

Their ordered `2 x 2` minors have signs

\[
 (+,+,-)
\tag{2}
\]

in both cases:

\[
 \det(1,i)=1,
 \quad
 \det(1,1+i)=1,
 \quad
 \det(i,1+i)=-1,
\]

and

\[
 \det(1,i)=1,
 \quad
 \det(1,\sqrt2+i)=1,
 \quad
 \det(i,\sqrt2+i)=-\sqrt2.
\]

With the trivial valuation, both realize the same oriented trivially-valuated `U_(2,3)` frame.

Their integer period groups are different:

\[
 \Gamma_v=\mathbb Z+i\mathbb Z+(1+i)\mathbb Z
 =\mathbb Z+i\mathbb Z,
\tag{3}
\]

which is discrete, whereas

\[
 \Gamma_w
 =\mathbb Z+i\mathbb Z+(\sqrt2+i)\mathbb Z
 =(\mathbb Z+\sqrt2\mathbb Z)+i\mathbb Z
\tag{4}
\]

is nondiscrete because `Z+sqrt(2) Z` is dense in `R`.

In fact

\[
 \overline{\Gamma_w}=\mathbb R+i\mathbb Z.
\tag{4a}
\]

For `x+ik`, choose integers `a_n,b_n` with `a_n+b_n sqrt(2)->x`; then
`a_n+b_n(sqrt(2)+i)+(k-b_n)i -> x+ik`. Hence

\[
 \mathbb C/\overline{\Gamma_v}\cong(\mathbb R/\mathbb Z)^2,
 \qquad
 \mathbb C/\overline{\Gamma_w}\cong\mathbb R/\mathbb Z.
\tag{4b}
\]

### Theorem 1.1

Oriented support plus trivial basis valuation does not determine the closure of the integral
period group, Hausdorff phase quotient, or existence of a discrete period lattice.

### Proof

The minor computation proves equality of the oriented trivially-valuated frame. Equations `(3)`
and `(4)` prove the period-closure fracture. Density of `Z+sqrt(2)Z` follows from irrational
rotation, or Dirichlet approximation applied to `sqrt(2)`. `[PROVED HERE]`

## 2. A complete positive current face does not orient its extension

For a finite positive measure `mu` supported on `(0,infinity)`, define factorial moments

\[
 s_k={1\over k!}\int t^k\,d\mu(t).
\tag{5}
\]

Take

\[
 \mu_+={16\over17}\delta_{3/4}+{1\over17}\delta_5,
 \qquad
 \mu_-={4\over5}\delta_{1/2}+{1\over5}\delta_3.
\tag{6}
\]

Direct calculation gives, for both carriers,

\[
 s_0=s_1=s_2=1.
\tag{7}
\]

Thus they have the identical positive size-one head, identical singular size-two Hankel face

\[
 \begin{pmatrix}1&1\\1&1\end{pmatrix},
\tag{8}
\]

and identical null polynomial `P=X-1`. Yet

\[
 s_3^+={31\over24},
 \qquad
 s_3^-={11\over12},
\tag{9}
\]

so the first extension/Krein crossings are

\[
 [P,XP]_+=s_3^+-s_2={7\over24}>0,
\qquad
 [P,XP]_- =s_3^--s_2=-{1\over12}<0.
\tag{10}
\]

For `f=sum_j f_jX^j` and `g=sum_k g_kX^k`, define

\[
 [f,g]_s=\sum_{j,k}f_jg_ks_{j+k}.
\tag{10a}
\]

Since `P=X-1`, `[P,XP]_s=s_3-2s_2+s_1=s_3-s_2` under `(7)`.

### Theorem 2.1

A complete current positive Hankel face, including its current minors and null circuit, together
with the fact that it admits a two-atom realization with strictly positive weights and nodes, does
not determine the sign of its first unseen affine extension.

### Proof

For `mu_+`,

\[
 s_1={16\over17}{3\over4}+{1\over17}5=1,
\]

\[
 s_2={1\over2}\left({16\over17}{9\over16}+{1\over17}25\right)=1,
\]

and

\[
 s_3={1\over6}\left({16\over17}{27\over64}+{1\over17}125\right)
 ={31\over24}.
\]

For `mu_-`,

\[
 s_1={4\over5}{1\over2}+{1\over5}3=1,
\]

\[
 s_2={1\over2}\left({4\over5}{1\over4}+{1\over5}9\right)=1,
\]

and

\[
 s_3={1\over6}\left({4\over5}{1\over8}+{1\over5}27\right)
 ={11\over12}.
\]

Equations `(8)`--`(10)` follow. `[PROVED HERE]`

## 3. The complete finite algebraic aperture tower does not determine its Hausdorff port

Let `X_0=c_00(P)` be finitely supported complex sequences on the primes and let

\[
 \varepsilon(x)=\sum_px_p,
 \qquad
 I=\ker\varepsilon.
\tag{11}
\]

Every finite algebraic aperture sees the same free prime frame and the same codimension-one
augmentation hyperplane. Complete the same algebraic diagram in different norms; the inherited
finite norms are not asserted numerically identical.

### Theorem 3.1

1. In `ell^1(P)`, `epsilon` extends continuously, `I` closes to `ker epsilon`, and

   \[
    \ell^1/\overline I\cong\mathbb C.
   \tag{12}
   \]

2. In `ell^2(P)`, `c_0(P)`, and `ell^p(P)` for every `1<p<infinity`, `I` is dense, so

   \[
    X/\overline I=0.
   \tag{13}
   \]

Thus all finite support, incidence, and augmentation data agree while the cofinal Hausdorff
quotient is either one-dimensional or zero.

### Proof

Continuity of `epsilon` on `ell^1` is immediate from
`|epsilon(x)|<=||x||_1`. Conversely, if `y in ker epsilon`, choose `x_n in c_00` with
`x_n->y` in `ell^1`, fix a prime `p_0`, and put
`z_n=x_n-epsilon(x_n)e_(p_0)`. Then `z_n in I` and

\[
 \|z_n-y\|_1\le\|x_n-y\|_1+|\varepsilon(x_n)|
 \le2\|x_n-y\|_1\longrightarrow0.
\]

Thus `closure(I)=ker epsilon`; surjectivity follows from `epsilon(e_(p_0))=1`, proving `(12)`.

For `ell^p`, `1<p<infinity`, fix `x in c_00` and let `S=epsilon(x)`. Choose `N` fresh prime coordinates and
let `u_N` equal `-S/N` on those coordinates and zero elsewhere. Then

\[
 \varepsilon(x+u_N)=0,
 \qquad
 \|u_N\|_p=|S|N^{1/p-1}\longrightarrow0.
\tag{14}
\]

Hence every `x in c_00` is approximated by elements of `I`; density of `c_00` proves density of
`I` in `ell^p`. For `c_0`, use the same correction and
`||u_N||_infinity=|S|/N->0`. This proves `(13)`. `[PROVED HERE]`

## 4. The combined incompleteness theorem

### Theorem 4.1 — three route-native static shadows are separately non-identifying

The following three route-native forgetful problems are separately non-identifiable:

1. oriented trivially-valued rank-two support does not determine integral period closure;
2. a current factorial Hankel face, its null line, and existence of a positive two-atom realization
   do not determine first-extension crossing sign;
3. the finite algebraic augmentation tower does not determine its Hausdorff quotient unless
   cofinal topology is supplied.

Consequently, no universal theory factoring routewise through only these respective static shadows
can recover all three outputs on every realization. Each output is individually independent of its
corresponding stated static shadow; no pairwise independence among the three outputs is asserted.

### Proof

If such an invariant determined period closure, the two triples in Section 1 would have the same
closure, contradiction. If it determined extension orientation, the two positive carriers in
Section 2 would have the same crossing sign, contradiction. If it determined the Hausdorff port,
the completions in Section 3 would have the same quotient, contradiction. `[PROVED HERE]`

## 5. Strongest positive survivor

These examples do not rule out a sufficiently rich coefficient object that explicitly contains
the missing data, and they do not prove a Cartesian product. They prove that a universal field must
admit typed reporter fibres for:

\[
 \boxed{
 \text{integral period closure}
 \quad\times\quad
 \text{affine first extension}
 \quad\times\quad
 \text{declared cofinal topology}.}
\tag{15}
\]

Together with the valuated Plücker--Gram law, this yields the finite constraint-frame hierarchy:

\[
 \text{support/rank}
 \to
 \text{event valuation}
 \to
 \text{unsquared phase/orientation}
 \to
 \text{positive capacity shadow},
\]

with laws specifying when period closure, affine extension, and cofinal topology exist and
transport between charts. A matroid is therefore a tangent frame of dependence, not by itself the
full law geometry.

Each reporter is separately forced by an exact pair sharing its corresponding route-native static
shadow.

## 6. Corpus scope

- Section 1 is the exact Gale period-closure fracture.
- Section 2 is the formalized Mass factorial positive-carrier orientation no-go.
- Section 3 is the prime-coframe completion/port uncertainty law.
- Route R supplies an additional cofinal warning: every finite diagonal Gamma intervention leaves
  the finite free frame unchanged, while the all-prime fixed-ideal action has a one-sided
  admission wall.

No RH consequence follows. The theorem tells a future field what data it must not erase.

## Lean-return notes

Existing formal parents include:

- `formal/GaloisForLFunctions/HTGeometry/GalePeriodClosureFracture.lean`;
- `formal/GaloisForLFunctions/HTGeometry/FactorialPositiveCarrierOrientationNoGo.lean`;
- prime completion/port formal modules cited by the parent completion card.

No Lean code was written or built in this campaign.

## Gates

- [x] period-closure countermodel proved
- [x] affine-extension orientation countermodel proved
- [x] completion-topology countermodel proved
- [x] combined impossibility proved
- [x] positive survivor extracted
- [x] whole-corpus hostile audit
- [ ] Lean wrapper theorem, if useful

## Log

- 2026-08-09 — created after literal Route G/L/O/R/Mass/E/Stokes/HT/recurrence audit rejected phased-valuated matroids as a complete universal carrier.
