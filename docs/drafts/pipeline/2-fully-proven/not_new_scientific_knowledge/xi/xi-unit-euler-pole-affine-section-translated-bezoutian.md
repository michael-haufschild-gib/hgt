# The unit Euler pole marks the Xi affine origin, and a translated Bezoutian classifies every real value fibre

- **ID:** `xi-unit-euler-pole-affine-section-translated-bezoutian`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / TOP-DOWN INTERFACE DISCHARGE / VALUE-FIBRE CLASSIFIER
- **Scientific status:** `[PROVED ON PAPER] [CLASSICAL-KERNEL BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `positive-jet-horizon-rh-level-blindness`,
  `projective-jet-horizon-stabilizer-law`, `RiemannTower.lean`, `ZetaCarrier.lean`
- **Statement:** The unit residue of the Euler source canonically selects the untranslated Xi fibre
  from its constant-translation orbit. For every real selected level, positivity of one explicit
  translated Xi Bezoutian is equivalent to placing the entire selected value fibre on the critical
  line.

## Goal

Positive-derivative horizon fields retain the constraint geometry of Xi but forget which target
value is called zero. The missing datum is not another derivative or projective invariant: it is an
affine-origin marking supplied by the Euler source. This card proves that the normalization of the
zeta pole supplies exactly that marking and then attaches an orientation-sensitive kernel to every
marked real value fibre.

The result discharges the extra affine-level assertion in a top-down RH chain. It does **not** prove
the remaining source positivity of the selected kernel.

## 1. The source-defined affine section

Put

\[
 A(s)=\frac{s(s-1)}2\,\pi^{-s/2}\Gamma(s/2)
\]

and let \(\xi\) have the normalization used in the formal library, so away from \(s=0,1\),

\[
 \xi(s)=A(s)\zeta(s).
\]

For an arbitrary \(c\in\mathbb C\), define on a punctured neighbourhood of \(1\)

\[
 Z_c(s)=\frac{\xi(s)-c}{A(s)}
       =\zeta(s)-\frac{c}{A(s)}.
\]

Then

\[
 \boxed{\lim_{s\to1}(s-1)Z_c(s)=1-2c.}                    \tag{1}
\]

Consequently,

\[
 \boxed{\operatorname*{Res}_{s=1}Z_c=1\iff c=0.}         \tag{2}
\]

Thus the unit Euler pole is a canonical affine section of the constant-translation orbit
\(\{\xi-c:c\in\mathbb C\}\). Positive jets are invariant under this orbit, but the source
normalization is not.

### Proof of (1)

The formal normalization of the Riemann zeta function gives

\[
 \lim_{s\to1}(s-1)\zeta(s)=1.                             \tag{3}
\]

Moreover \(\pi^{-1/2}\Gamma(1/2)=1\), and hence

\[
 \lim_{s\to1}\frac{A(s)}{s-1}=\frac12,
 \qquad
 \lim_{s\to1}\frac{s-1}{A(s)}=2.                        \tag{4}
\]

Multiplying the displayed formula for \(Z_c\) by \(s-1\) and applying (3)--(4) gives
\(1-2c\). Equation (2) follows immediately.

## 2. The translated value-fibre Bezoutian

Fix \(c\in\mathbb R\) and center at the critical line:

\[
 X_c(w)=\xi\!\left(\frac12+w\right)-c.
\]

The functional equation and Schwarz reality make \(X_c\) even and real-entire. On the right half
plane \(\mathbb H_+=\{w:\Re w>0\}\), define the Hermitian kernel

\[
 B_c(w,v)=
 \frac{X_c'(w)\overline{X_c(v)}+X_c(w)\overline{X_c'(v)}}
      {w+\bar v}.                                         \tag{5}
\]

The denominator never vanishes on \(\mathbb H_+\times\mathbb H_+\). The following exact
classification holds:

\[
 \boxed{
 B_c\succeq0\text{ on }\mathbb H_+
 \iff
 \bigl(\xi(s)=c\Longrightarrow\Re s=\tfrac12\bigr).
 }                                                        \tag{6}
\]

Here \(B_c\succeq0\) means that every finite Gram matrix
\((B_c(w_i,w_j))_{i,j}\) is positive semidefinite.

### Proof: critical value fibre implies kernel positivity

Assume every zero of \(X_c\) lies on the imaginary axis. Since \(X_c\) is even, real-entire, and
of order at most one, it is an entire function of \(w^2\) of order at most \(1/2<1\). Hadamard
factorization therefore has genus zero and no nonconstant exponential factor:

\[
 X_c(w)=Cw^{2m}\prod_n\left(1+\frac{w^2}{t_n^2}\right),
 \qquad C\in\mathbb R\setminus\{0\},\quad t_n>0.          \tag{7}
\]

Repeated factors retain multiplicity. Logarithmic differentiation gives, locally uniformly away
from the zeros,

\[
 L_c(w):=\frac{X_c'(w)}{X_c(w)}
 =\frac{2m}{w}+\sum_n\frac{2w}{w^2+t_n^2}.                \tag{8}
\]

For \(w,v\in\mathbb H_+\), each summand has a positive finite-rank divided kernel:

\[
 \frac{2m/w+2m/\bar v}{w+\bar v}=\frac{2m}{w\bar v},     \tag{9}
\]

and

\[
 \frac{2w/(w^2+t^2)+2\bar v/(\bar v^2+t^2)}{w+\bar v}
 =2\left(
 \frac{w}{w^2+t^2}\overline{\frac{v}{v^2+t^2}}
 +\frac{t}{w^2+t^2}\overline{\frac{t}{v^2+t^2}}
 \right).                                                \tag{10}
\]

Equations (8)--(10) show that

\[
 \frac{L_c(w)+\overline{L_c(v)}}{w+\bar v}
\]

is positive semidefinite. Multiplying a positive kernel by
\(X_c(w)\overline{X_c(v)}\) preserves positivity and gives (5). Continuity extends the conclusion
across the zeros of \(X_c\).

### Proof: an off-axis value point destroys positivity

Conversely, suppose \(X_c(a)=0\) for some \(a\in\mathbb H_+\), with multiplicity \(m\ge1\). For
small real \(t>0\), put \(w=a-t\), which remains in \(\mathbb H_+\). Local factorization at \(a\)
gives

\[
 \frac{X_c'(w)}{X_c(w)}=-\frac mt+O(1).                  \tag{11}
\]

On the diagonal,

\[
 B_c(w,w)=|X_c(w)|^2
 \frac{\Re(X_c'(w)/X_c(w))}{\Re w}.                      \tag{12}
\]

Equations (11)--(12) make \(B_c(w,w)<0\) for sufficiently small \(t\), contradicting positive
semidefiniteness. Finally, evenness sends every zero with negative real part to one with positive
real part. Therefore positivity excludes every zero off the imaginary axis and proves (6).

## 3. The marked top-down RH chain

Combining (2) and (6) yields

\[
 \boxed{
 \mathrm{RH}
 \iff
 \exists c\in\mathbb R:\quad
 \operatorname*{Res}_{s=1}Z_c=1
 \quad\text{and}\quad
 B_c\succeq0\text{ on }\mathbb H_+.
 }                                                        \tag{13}
\]

The two conditions have different jobs:

1. the unit Euler residue forces \(c=0\) and marks the target origin;
2. the Bezoutian positivity orients the selected fibre.

This is the positive replacement for the horizon blindness theorem. The horizon geometry may be
used to classify the translation orbit; the Euler source supplies a canonical section through
that orbit; the translated Bezoutian tests the divisor orientation on the selected section.

## 4. Exact remaining open theorem

Equation (13) is not a proof of RH because the following source implication remains open:

\[
 \boxed{
 \text{explicit prime--Gamma/Euler source law for the unit-residue section}
 \Longrightarrow B_0\succeq0.
 }                                                        \tag{14}
\]

The value of the affine-section theorem is that (14) no longer needs an extra assumption saying
which translate is canonical. A proof may target the unique unit-residue fibre from the outset.
No zero locations, real-rootedness, anti-Herglotzness, or RH-equivalent positive measure may be
used to prove (14).

## 5. Existing Lean parents and formalization surface

The formal corpus already contains the source ingredients:

- `RHTower/ZetaCarrier.lean`: `archFactor` and `xi_eq_archFactor_mul_zeta`;
- `RHTower/RiemannTower.lean`: the entire `xi`, its reflection, and `xi_one : xi 1 = 1/2`;
- `RHTower/ZetaLogDerivResidue.lean`: `zetaResidueUnit` and the unit zeta residue;
- `RHTower/CCMShiftedXiCancellation.lean`: an entire pole-filled version of
  `(s-1) * riemannZeta s`;
- `HTGeometry/ProjectiveJetHorizon.lean`: `jetTailField_constSlopeAffine_eq`, which formalizes the
  translation blindness repaired here.

The missing Lean layer is theorem packaging, not a new hypothesis:

1. define the punctured translated decompletion `Z_c`;
2. prove `(s-1) * Z_c(s) -> 1-2c` from the existing unit-residue theorem and continuity of the
   archimedean factor at `1`;
3. define `X_c` and `B_c`;
4. formalize the genus-zero even-entire factorization or an equivalent Hermite--Biehler kernel
   theorem needed for (6).

No Lean formalization is claimed by this card.

## Literature calibration

The Hadamard-factorization and positive-kernel mechanism is classical. Horizontal monotonicity of
the completed zeta function under RH is also known; for example, Sondow and Dumitrescu prove a
[closely related conditional monotonicity criterion](https://arxiv.org/abs/1005.1104). The
contribution here is only the exact splice to this corpus: the zeta unit residue repairs the
affine-origin blindness of the positive-jet horizon and yields the marked value-fibre chain (13).
No novelty claim is made.

## Gates

- [x] 0 -> 1: source-pure affine marking and orientation kernel identified
- [x] 1 -> 2: complete symbolic proofs of the residue law and the two directions of the kernel
  classifier
- [ ] 2 -> 3: Lean formalization of the punctured residue limit and the analytic kernel theorem
- [ ] 3 -> 4: standalone presentation and formal certificate
