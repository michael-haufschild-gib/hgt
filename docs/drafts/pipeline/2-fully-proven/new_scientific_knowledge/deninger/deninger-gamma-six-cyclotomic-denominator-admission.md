# Gamma-six cyclotomic denominator admission

- **Stage:** 2 — dependency-closed paper proof
- **Type:** SOURCE-SUPPORT CORRECTION / MIXED COEFFICIENT ADMISSION / ROUTE-L FRONTIER ADVANCE
- **Status:** PAPER-PROVED / PROJECT-SPECIFIC NEW KNOWLEDGE / NOT RH / NO LEAN WORK DURING CORPUS REFACTOR
- **Parents:** `deninger-mobius-gamma-six-normal-transgression.md` and
  `deninger-gamma-six-orientation-residue-wall.md`
- **Corpus inputs:** `DeningerRationalWittFiniteEvaluationBridge.lean`,
  `DeningerRationalWittGaugeFirstSuspensionDescent.lean`,
  `DeningerCalderonWittAlgebraicSource.lean`, and
  `DeningerCalderonWittSingularGammaTransgression.lean`.

## 1. Frontier correction

The Gamma-six normal is extracted from the unique complementary rational pair

\[
 x_m=\frac{6^m}{1+6^m},\qquad
 y_m=\frac1{1+6^m},\qquad x_m+y_m=1.
\tag{1}
\]

Its normalized output has ratio (x_m/y_m=6^m), so the final Kummer normal is supported only
at the archimedean, (2)-adic, and (3)-adic clock faces. That does not mean the strict source
cell has only those places. Before the normal selector and the multiplication by ([y_m]^{-1}),
every prime divisor of (1+6^m) is a genuine place of both entries in (1).

This distinction was absent from the previous Route-L frontier. It is load-bearing because the
denominator places are invisible to the scalar Kummer regulator and to the first tame-symbol
boundary, but visible to the rational-Witt packet. Consequently a strict source comparison cannot
replace the honest Steinberg cell by its already-normalized three-place shadow.

## 2. Denominator places are infinite and cofinal

Put

\[
                         d_m=1+6^m.
\tag{2}
\]

Every prime divisor of (d_m) is different from (2) and (3).

### Theorem 2.1 — infinitely many cyclotomic denominator places

The set

\[
 \mathcal L_6=\{\ell\text{ prime}:\ell\mid 1+6^m
                         \text{ for some }m\ge1\}
\tag{3}
\]

is infinite.

### Proof

Assume that (mathcal L_6=S) is finite. For every (ell\in S), let
(o_ell=\operatorname{ord}_ell(6)). Since (ellmid 6^m+1) for some (m), the order
(o_ell) is even. Let

\[
                         M=\operatorname{lcm}_{\ell\in S}o_ell.
\]

Then (6^M\equiv1\pmodell) for every (ell\in S). On the other hand, the odd integer
(6^M+1>1) has a prime divisor (r). By the definition of (S), one has (r\in S), hence
simultaneously

\[
                       6^M\equiv1\pmod r,
                       \qquad 6^M\equiv-1\pmod r.
\]

Thus (rmid2), contradicting that (6^M+1) is odd. ∎

The proof gives a source-defined recursive family. Start with

\[
                         m_1=1,\qquad \ell_1=7.
\tag{4}
\]

After (ell_1,\ldots,\ell_k) have been chosen, put

\[
 m_{k+1}=\operatorname{lcm}_{1\le j\le k}
               \operatorname{ord}_{\ell_j}(6)
\tag{5}
\]

and let (ell_{k+1}) be the least prime divisor of (6^{m_{k+1}}+1). No previously chosen
prime divides that integer, by (5). Moreover
(operatorname{ord}_{\ell_{k+1}}(6)
 \nmid m_{k+1}) but divides (2m_{k+1}), so the next least common multiple is strictly larger.
Thus

\[
 m_1<m_2<\cdots,\qquad
 \ell_i\ne\ell_j\quad(i\ne j).
\tag{6}
\]

No primitive-divisor theorem is needed for this cofinal family.

## 3. Tame-null and Kummer-null, but Witt-visible

Fix (m\ge1), let (ellmid d_m), and write

\[
                         e=v_ell(d_m)>0.
\]

Since (gcd(6,d_m)=1), equation (1) gives

\[
 v_ell(x_m)=v_ell(y_m)=-e,
 \qquad
 v_ell(x_m/y_m)=0,
 \qquad
 \overline{x_m/y_m}=\overline{6^m}=-1
       \quad\text{in }\mathbb F_ell^	imes.
\tag{7}
\]

### Theorem 3.1 — exact tame and Kummer invisibility

At every denominator place (ellmid d_m),

\[
 \partial_ell\{x_m,y_m\}=1,
 \qquad
 \log|x_m/y_m|_ell=0.
\tag{8}
\]

### Proof

The second identity is immediate from (7). For the tame symbol, use

\[
 \partial_ell\{x,y\}
  =(-1)^{v_ell(x)v_ell(y)}
    \overline{x^{v_ell(y)}y^{-v_ell(x)}}.
\]

With both valuations equal to (-e), this becomes

\[
 (-1)^{e^2}\overline{(y_m/x_m)^e}
 =(-1)^e\overline{6^{-me}}
 =(-1)^e(-1)^e=1.
\]

Here (e^2\equiv e\pmod2) and (6^m\equiv-1\pmodell). ∎

The first Rost--Schmid residue and the scalar logarithmic regulator therefore both erase this
place. The rational-Witt packet does not.

Let

\[
                         n_{m,\ell}=\operatorname{ord}_ell(6).
\tag{9}
\]

Then (n_{m,ell}) is even, (n_{m,ell}mid2m),
(n_{m,ell}\nmid m), and (n_{m,ell}midell-1). In particular, the stage modulus
(n_{m,ell}) is prime to (ell), and arithmetic Frobenius acts trivially on that cyclotomic
stage because

\[
                         \ell\equiv1\pmod{n_{m,\ell}}.
\tag{10}
\]

### Theorem 3.2 — denominator Witt packet survives Frobenius descent

Let (ar6\in\mathbb F_ell^	imes) be the residue of (6), of order (n_{m,ell}). In the
complexified rational-Witt group-algebra presentation at (ell), the element

\[
                         \eta_{m,ell}=[\bar6]-[1]
\tag{11}
\]

is nonzero, fixed by arithmetic Frobenius, and has a nonzero finite cyclotomic packet evaluation.

### Proof

The two basis vectors in (11) are distinct because (ar6) has order at least two. Both lie in
(mathbb F_ell^	imes), so Frobenius (u\mapsto u^ell) fixes them separately. Identify the
cyclic group generated by (ar6) with (mathbb Z/n_{m,ell}mathbb Z), sending (1) to
(ar6). Evaluation at the primitive character sends (11) to

\[
                  \exp(2\pi i/n_{m,ell})-1\ne0.
\]

This is exactly one of the finite cyclotomic evaluations used by the rational-Witt packet
presentation. ∎

Thus denominator-place cancellation occurs only after forgetting finite packet data. At the
strict source level it is a nonzero, Frobenius-fixed rational-Witt class.

## 4. Source-first mixed coefficient topology

Apply the construction above to the recursive family ((m_k,\ell_k)) from (4)--(6). Put

\[
 n_k=\operatorname{ord}_{\ell_k}(6)
\]

and let (z_k) be the normalized nonzero finite packet vector obtained from
(eta_{m_k,ell_k}). Different (k) belong to different prime summands, so the (z_k) are
orthonormal in the Hilbert direct sum of packet spaces.

Define the Köthe source

\[
 \mathcal E_{\Gamma,6}=
 \left\{c=(c_k^+,c_k^-)_{k\ge1}:
   q_a(c):=\sum_{k\ge1}6^{a m_k}
        (|c_k^+|+|c_k^-|)<\infty
   \text{ for every }0<a<1\right\}.
\tag{12}
\]

It is enough to take a countable cofinal family of rational (a\uparrow1). The unweighted
(ell^1) norm, and hence the unweighted (ell^2) norm, is continuous on this space.

### Theorem 4.1 — the coefficient space is nuclear

(mathcal E_{Gamma,6}) is a nuclear Fréchet Köthe space, continuously embedded in the mixed
(ell^1/\ell^2) packet carrier.

### Proof

For (0<a<b<1), the ratio of the two Köthe weights is

\[
                         6^{-(b-a)m_k}.
\]

The integers (m_k) are strictly increasing, hence (m_k\ge k), and therefore

\[
             \sum_{k\ge1}6^{-(b-a)m_k}
             \le\sum_{k\ge1}6^{-(b-a)k}<\infty.
\tag{13}
\]

The bonding map from the (b)-weighted (ell^1) step to the (a)-weighted step is thus a
nuclear diagonal map. The standard projective-limit criterion for Köthe echelon spaces proves
nuclearity. Since all weights are at least one, (q_a) dominates the unweighted (ell^1) norm,
which dominates (ell^2). ∎

For a real horizontal displacement (delta) with (|\delta|<1), define the packet evaluation

\[
 \operatorname{Ev}_\delta(c)
  =\bigoplus_{k\ge1}
    \left(c_k^+6^{m_k\delta}
          +c_k^-6^{-m_k\delta}\right)z_k.
\tag{14}
\]

### Theorem 4.2 — continuous source-first evaluation on the whole open strip

For every (|\delta|<1), (14) is a continuous map

\[
       \operatorname{Ev}_\delta:
       \mathcal E_{\Gamma,6}\longrightarrow
       \bigoplus
       {}^{\ell^1}_{k\ge1}\mathcal P_{\ell_k,n_k}
       \hookrightarrow
       \bigoplus
       {}^{\ell^2}_{k\ge1}\mathcal P_{\ell_k,n_k}.
\tag{15}
\]

### Proof

Choose (a) with (|\delta|<a<1). Then

\[
\begin{aligned}
 \|\operatorname{Ev}_\delta(c)\|_{\ell^1}
 &\le\sum_k6^{|\delta|m_k}(|c_k^+|+|c_k^-|)\\
 &\le q_a(c).
\end{aligned}
\]

The inclusion (ell^1\hookrightarrowell^2) is continuous. ∎

## 5. Canonical tensor-square Gamma-six grade

The complete corrected tail satisfies

\[
 H_{6,m}=6^{-m/2}U_{-m\log6}R_{6,m}.
\tag{16}
\]

Thus its tensor-square scale is exactly (6^{-m}), independently of any Xi zero. This forces the
source vector

\[
 \gamma_6=(c_k^+,c_k^-)_{k\ge1},
 \qquad
 c_k^+=6^{-m_k},\qquad c_k^-=-6^{-m_k}.
\tag{17}
\]

For every (a<1),

\[
 q_a(\gamma_6)
   =2\sum_k6^{-(1-a)m_k}<\infty,
\]

so (gamma_6\in\mathcal E_{Gamma,6}).

### Theorem 5.1 — unconditional mixed admission of the full-grade oriented character

For every real (|\delta|<1),

\[
 \boxed{
 \mathcal W_6(\delta):=\operatorname{Ev}_\delta(\gamma_6)
 =\bigoplus_{k\ge1}6^{-m_k}
   \left(6^{m_k\delta}-6^{-m_k\delta}\right)z_k
 \in\ell^1\cap\ell^2.}
\tag{18}
\]

It satisfies

\[
 \mathcal W_6(-\delta)=-\mathcal W_6(\delta),
 \qquad
 \mathcal W_6(\delta)=0\Longleftrightarrow\delta=0.
\tag{19}
\]

The first coordinate recovers the fixed physical Gamma-six coefficient:

\[
 \operatorname{coord}_1\mathcal W_6(\delta)
   =6^{-1}(6^\delta-6^{-\delta})z_1.
\tag{20}
\]

### Proof

Only (19) needs proof beyond Theorem 4.2. Reflection oddness is termwise. If (delta=0), every
coefficient vanishes. Conversely, (m_1=1) and (z_1\ne0), so vanishing of the first coordinate
gives (6^\delta=6^{-\delta}), hence (delta=0). Equation (20) is the (k=1) component. ∎

For every nontrivial Xi zero (ho), one has

\[
                       \delta_\rho=2\Re\rho-1\in(-1,1).
\]

Therefore (18) is an unconditional, source-first, place-resolved mixed
(ell^1/\ell^2) admission of the full Gamma-six orientation on every actual divisor fibre. It
uses no divisor-dependent horizon grade. The grade (6^{-m}) comes from the tensor square of the
complete Möbius source itself.

## 6. Pole-pair admission and the exact remaining wall

Tensoring (17) with the canonical meromorphic pair

\[
 \left(B_6(s),
       -\frac{A(s)}{A(1-s)}B_6(1-s)\right)
\tag{21}
\]

gives a coefficientwise mixed-admissible pole pair on every fixed divisor germ. The two principal
parts cancel on the codiagonal by the functional equation. Keeping the two orientation slots and
the (z_k) labels retains the antidiagonal (18). Hence the following are now proved rather than
left as topology conjectures:

1. the honest Gamma-six source requires a cofinal family of denominator places;
2. those places are zero under tame and logarithmic Kummer residue but nonzero in rational-Witt
   packets;
3. their finite cyclotomic stages are Frobenius-trivial, so arithmetic descent retains the whole
   packet instead of averaging it away;
4. the tensor-square complete-source grade gives a nuclear source and simultaneous mixed
   (ell^1/\ell^2) admission throughout the open strip;
5. the fixed physical (m=1) coefficient survives as a bounded coordinate of that completion.

This does not prove Route-L annihilation. In fact the completion makes the remaining obstruction
sharper. Let (	au_k) be the normalized packet coordinate with (	au_k(z_k)=1). The continuous
(ell^1) codiagonal reader gives

\[
 \Tau(\mathcal W_6(\delta))
 =\sum_{k\ge1}6^{-m_k}
       \left(6^{m_k\delta}-6^{-m_k\delta}\right).
\tag{22}
\]

Every summand has the sign of (delta). Therefore

\[
                 \Tau(\mathcal W_6(\delta))=0
                 \Longleftrightarrow\delta=0.
\tag{23}
\]

Frobenius descent, positive packet averaging, and scalar functional-equation cancellation cannot
annihilate the resolved class. The strict theorem still missing is a source-derived **relative
chain differential**, formed before the normal selector forgets the denominator places, which
maps the pole pair and all denominator packets into the existing Meyer--Calderón target and makes
the fixed Burnol/Deninger reader cyclic on that transported boundary. Equation (23) proves that
the differential must be signed and non-principal; no cooriented packet trace can supply it.

The corrected place set is at least

\[
 \{\infty,2,3,5\}
 \cup\{\ell_k:k\ge1\}.
\tag{24}
\]

Here (5) belongs to the finite correction defining (B_6), while the cofinal (ell_k) belong
to the honest Steinberg-normal source before denominator cancellation. The old fixed
({\infty,2,3\}) description was only the normalized clock polygon, not the full source.

## 7. Heavy conjecture audit

1. **Conjecture:** the honest Gamma-six Steinberg source has only the normalized
   (infty,2,3) place support. **Falsified.** Equation (1) forces every prime divisor of
   (1+6^m), and Theorem 2.1 proves these places are infinite.
2. **Conjecture:** equal denominator valuations make those places irrelevant to strict descent.
   **Falsified with a positive survivor.** They are tame-null and Kummer-null by Theorem 3.1 but
   rational-Witt-visible by Theorem 3.2.
3. **Conjecture:** arithmetic Frobenius averaging kills the surviving denominator packet.
   **Falsified maximally.** Its source cyclotomic stage has
   (ell\equiv1\pmod n), so Frobenius acts as the identity.
4. **Conjecture:** cofinal denominator support prevents any mixed Hilbert admission.
   **Falsified constructively.** The tensor-square source scale (6^{-m}) produces the nuclear
   Köthe carrier and the unconditional mixed admission (18).
5. **Conjecture:** admitted packet averaging plus pole cancellation supplies the missing zero.
   **Falsified sharply.** The resolved antidiagonal has the sign-definite trace (22), whose zero
   set is exactly the critical line.

## 8. Novelty and hostile audit

- Infinitude of prime divisors of (6^m+1), tame-symbol calculation, finite cyclic characters,
  and the Köthe nuclearity criterion are classical ingredients; no independent novelty is claimed
  for them.
- Project-specific new knowledge is their forced fusion with the honest Gamma-six Steinberg
  normal: denominator places are precisely the source data lost between the Steinberg cell and
  its normalized (6^m) output.
- The source-derived tensor-square grade (6^{-m}) gives a coefficient-faithful mixed admission
  for the entire open critical strip, not merely for one selected divisor configuration.
- The construction neither assumes nor proves the fixed-reader zero. Equations (19), (20), and
  (23) explicitly retain the RH-bearing class.
- No numerical experiment, Xi-zero location, positivity premise, reflected compatibility, new
  coefficient reader, or quotient defined by the desired kernel is used.

## 9. Frontier ledger

- [x] identify full pre-normal place support of the Gamma-six Steinberg cell
- [x] prove denominator places form an infinite cofinal family
- [x] prove exact tame/Kummer invisibility and rational-Witt visibility
- [x] prove denominator cyclotomic stages survive Frobenius descent without orbit collapse
- [x] construct nuclear source-first mixed (ell^1/\ell^2) coefficient topology
- [x] admit full-grade Gamma-six orientation on every nontrivial Xi divisor fibre
- [x] retain fixed physical (m=1) coefficient as a bounded coordinate
- [x] rule out cooriented packet averaging as annihilator
- [ ] construct strict relative Rost--Schmid-to-Meyer chain differential on the full place family
- [ ] prove fixed Burnol/Deninger reader cyclic on that transported boundary
