# Gamma-six cyclotomic denominator parity wall

- **Stage:** 3 — formalized in Lean 4
- **Type:** SOURCE-SUPPORT CORRECTION / SHARP PARITY NO-GO / POSITIVE EVEN ADMISSION
- **Status:** FORMALIZED / PROJECT-SPECIFIC NEW KNOWLEDGE / NOT RH
- **Parents:** deninger-mobius-gamma-six-normal-transgression.md and
  deninger-gamma-six-orientation-residue-wall.md
- **Corpus inputs:** DeningerRationalWittFiniteEvaluationBridge.lean,
  DeningerRationalWittGaugeFirstSuspensionDescent.lean,
  DeningerCalderonWittAlgebraicSource.lean, and
  DeningerCalderonWittSingularGammaTransgression.lean.

## 1. Frontier correction

The Gamma-six normal is extracted from the unique complementary rational pair

\[
 x_m=\frac{6^m}{1+6^m},\qquad
 y_m=\frac1{1+6^m},\qquad x_m+y_m=1.
\tag{1}
\]

Its normalized outputs are

\[
 [y_m]^{-1}Q_m(N)P_m=[6^m]-1,
 \qquad
 [x_m]^{-1}Q_m^{\mathrm{op}}(N)P_m=[6^{-m}]-1.
\tag{2}
\]

The difference is the reflection-odd physical class

\[
                         [6^m]-[6^{-m}].
\tag{3}
\]

Because the ratios in (2) are \(6^{\pm m}\), the final Kummer normal has only the
\(\infty,2,3\) clock support. Before normal extraction, however, both entries of (1) have a pole
at every prime dividing \(1+6^m\). A strict pre-normal source comparison must classify these
denominator places before it discards them.

The classification below has two parts:

1. the denominator layer is nonzero and rational-Witt visible even though its tame symbol and
   logarithmic Kummer regulator vanish;
2. the two normal orientations have exactly the same denominator residue, so this entire layer is
   reflection-even and cannot cancel the reflection-odd class (3).

The second point is the hostile correction. Merely attaching the physical coefficient (3) to a
nonzero denominator packet would be an added coefficient map, not a consequence of the honest
Steinberg cell.

## 2. Denominator places are infinite and cofinal

Put

\[
                         d_m=1+6^m.
\tag{4}
\]

Every prime divisor of \(d_m\) is different from \(2\) and \(3\).

### Theorem 2.1 — infinitely many cyclotomic denominator places

The set

\[
 \mathcal L_6=\{\ell\text{ prime}:\ell\mid 1+6^m
                         \text{ for some }m\ge1\}
\tag{5}
\]

is infinite.

### Proof

Assume that \(\mathcal L_6=S\) is finite. For every \(\ell\in S\), let
\(o_\ell=\operatorname{ord}_\ell(6)\), and put

\[
                         M=\operatorname{lcm}_{\ell\in S}o_\ell.
\]

Then \(6^M\equiv1\pmod\ell\) for every \(\ell\in S\). The odd integer \(6^M+1>1\) has a prime
divisor \(r\). By definition of \(S\), one has \(r\in S\). Hence

\[
                         6^M\equiv1\equiv-1\pmod r,
\]

so \(r\mid2\), contradicting that \(6^M+1\) is odd. ∎

The proof gives a source-defined recursive family. Start with

\[
                         m_1=1,\qquad \ell_1=7.
\tag{6}
\]

After \(\ell_1,\ldots,\ell_k\) have been chosen, put

\[
 m_{k+1}=\operatorname{lcm}_{1\le j\le k}
               \operatorname{ord}_{\ell_j}(6)
\tag{7}
\]

and let \(\ell_{k+1}\) be the least prime divisor of \(6^{m_{k+1}}+1\). No previously chosen
prime divides that integer. Moreover
\(\operatorname{ord}_{\ell_{k+1}}(6)\nmid m_{k+1}\) but divides \(2m_{k+1}\), so the next least
common multiple is strictly larger. Thus

\[
 m_1<m_2<\cdots,\qquad
 \ell_i\ne\ell_j\quad(i\ne j).
\tag{8}
\]

No primitive-divisor theorem is needed.

## 3. Tame and Kummer invisibility

Fix \(m\ge1\), let \(\ell\mid d_m\), and put

\[
                         e=v_\ell(d_m)>0.
\]

Since \(\gcd(6,d_m)=1\), equation (1) gives

\[
 v_\ell(x_m)=v_\ell(y_m)=-e,
 \qquad
 v_\ell(x_m/y_m)=0,
 \qquad
 \overline{x_m/y_m}=\overline{6^m}=-1
       \quad\text{in }\mathbb F_\ell^\times.
\tag{9}
\]

### Theorem 3.1 — exact tame and Kummer invisibility

At every denominator place \(\ell\mid d_m\),

\[
 \partial_\ell\{x_m,y_m\}=1,
 \qquad
 \log|x_m/y_m|_\ell=0.
\tag{10}
\]

### Proof

The second identity follows from (9). For the tame symbol,

\[
 \partial_\ell\{x,y\}
  =(-1)^{v_\ell(x)v_\ell(y)}
    \overline{x^{v_\ell(y)}y^{-v_\ell(x)}}.
\]

With both valuations equal to \(-e\), this is

\[
 (-1)^{e^2}\overline{(y_m/x_m)^e}
 =(-1)^e\overline{6^{-me}}
 =(-1)^e(-1)^e=1.
\]

Here \(e^2\equiv e\pmod2\) and \(6^m\equiv-1\pmod\ell\). ∎

Thus the first Rost--Schmid residue and scalar logarithmic regulator erase the denominator place.
This does not imply rational-Witt packet vanishing.

## 4. Exact common-pole normal residue

On the span of group-basis terms of valuation \(-e\), define common-pole reduction by

\[
 \operatorname{red}_{\ell,e}([u])
     =[\overline{\ell^e u}]
     \in\mathbb C[\mathbb F_\ell^\times].
\tag{11}
\]

Let

\[
 \bar y_{m,\ell}=\overline{\ell^e y_m}\in\mathbb F_\ell^\times.
\]

The archimedean normal selector satisfies

\[
                         Q_m(N)P_m=[x_m]-[y_m].
\tag{12}
\]

### Theorem 4.1 — forward denominator residue

The translated common-pole residue of (12) is

\[
 \boxed{
 [\bar y_{m,\ell}]^{-1}
   \operatorname{red}_{\ell,e}\bigl(Q_m(N)P_m\bigr)
   =[-1]-[1].}
\tag{13}
\]

### Proof

By (11)--(12),

\[
\begin{aligned}
 [\bar y_{m,\ell}]^{-1}
   \operatorname{red}_{\ell,e}([x_m]-[y_m])
 &= [\overline{x_m/y_m}]-[1]\\
 &= [-1]-[1]
\end{aligned}
\]

by (9). ∎

The opposite selector swaps \(x_m\) and \(y_m\), giving

\[
                         Q_m^{\mathrm{op}}(N)P_m=[y_m]-[x_m].
\tag{14}
\]

### Theorem 4.2 — reciprocal denominator residue is identical

Writing
\(\bar x_{m,\ell}=\overline{\ell^e x_m}\), one has

\[
 \boxed{
 [\bar x_{m,\ell}]^{-1}
   \operatorname{red}_{\ell,e}\bigl(Q_m^{\mathrm{op}}(N)P_m\bigr)
   =[-1]-[1].}
\tag{15}
\]

### Proof

Equations (9), (11), and (14) give

\[
 [\bar x_{m,\ell}]^{-1}
   \operatorname{red}_{\ell,e}([y_m]-[x_m])
 =[\overline{y_m/x_m}]-[1]
 =[-1]-[1],
\]

because \((-1)^{-1}=-1\). ∎

### Corollary 4.3 — denominator orientation collapse

The reflection-odd difference of the two normalized denominator residues is zero:

\[
             ([-1]-[1])-([-1]-[1])=0.
\tag{16}
\]

Equivalently, direct reduction of the final oriented normal gives

\[
          [\overline{6^m}]-[\overline{6^{-m}}]
          =[-1]-[-1]=0.
\tag{17}
\]

Thus denominator places are present before the normal selector but lie entirely in the
reflection-even sector after common-pole normalization.

## 5. Nonzero rational-Witt survivor

Put

\[
                         \varepsilon_\ell=[-1]-[1]
       \in\mathbb C[\mathbb F_\ell^\times].
\tag{18}
\]

Every denominator prime is odd, so \(-1\ne1\) in \(\mathbb F_\ell^\times\).

### Theorem 5.1 — even residue survives rational-Witt descent

\(\varepsilon_\ell\) is nonzero, fixed by arithmetic Frobenius, and has nonzero evaluation at
the order-two cyclotomic character:

\[
                         \operatorname{ev}_{-}(\varepsilon_\ell)=-2.
\tag{19}
\]

### Proof

The two group-basis vectors in (18) are distinct. Frobenius \(u\mapsto u^\ell\) fixes both
\(\pm1\). The sign character sends \([-1]\) to \(-1\) and \([1]\) to \(1\), proving (19). This
is the modulus-two finite cyclotomic packet in the complexified rational-Witt presentation, and
\(\ell\equiv1\pmod2\), so its Frobenius action is the identity. ∎

There is also a larger Frobenius-fixed stage generated by \(\bar6\), of modulus
\(\operatorname{ord}_\ell(6)\). Its element \([\bar6]-[1]\) is nonzero. But equations
(13)--(17) show that this larger root packet is **not** the residue of the oriented normal.
Using it with coefficient \(6^{m\delta}-6^{-m\delta}\) would add precisely the non-principal
signed comparison Route L is missing. It cannot be counted as a denominator consequence.

## 6. Mixed admission of the even denominator layer

Use the cofinal family \((m_k,\ell_k)\) from (6)--(8), and let \(z_k\) be the normalized
order-two packet vector obtained from \(\varepsilon_{\ell_k}\). Different \(k\) lie in different
prime summands.

For every honest convergence grade \(m\ge3\), the complete corrected tail has half-density factor
\(6^{-m/2}\). Its tensor-square factor is \(6^{-m}\). Extending this same ordinary-integer law
over the two finite grades \(m=1,2\), define

\[
                         \mathcal E_6
       =\bigoplus_{k\ge1}6^{-m_k}z_k.
\tag{20}
\]

### Theorem 6.1 — unconditional mixed admission

\[
                         \mathcal E_6\in\ell^1\cap\ell^2.
\tag{21}
\]

Moreover \(\mathcal E_6\) is reflection-even.

### Proof

Since \(m_k\ge k\),

\[
 \sum_k6^{-m_k}\le\sum_k6^{-k}<\infty,
 \qquad
 \sum_k6^{-2m_k}\le\sum_k6^{-2k}<\infty.
\]

Reflection fixes every \(z_k\) by Corollary 4.3. ∎

The natural Köthe refinement

\[
 \mathcal E_{\Gamma,6}^{+}
 =\left\{c=(c_k):
   \sum_k6^{a m_k}|c_k|<\infty
   \text{ for every }0<a<1\right\}
\tag{22}
\]

is a nuclear Fréchet space. Indeed, for \(0<a<b<1\),

\[
                    \sum_k6^{-(b-a)m_k}<\infty,
\tag{23}
\]

so every bonding inclusion is nuclear. Thus topology and cofinal support of the denominator layer
are completely controlled. They do not contribute to the odd physical obstruction.

## 7. Sharp mixed admission of the actual odd pole pair

The failure of denominator repair does not obstruct coefficient admission of the two actual
normal orientations. Keep those orientations as two separate slots and use the tensor-square
half-density grade forced by the complete source:

\[
 \Gamma_6=
 \left(6^{-m}[6^m],-6^{-m}[6^{-m}]\right)_{m\ge1}.
\tag{24}
\]

This is the actual oriented Kummer normal, not a coefficient attached to an unrelated finite
packet.

Define the two-slot Köthe source

\[
 \mathcal K_{\Gamma,6}=
 \left\{c=(c_m^+,c_m^-)_{m\ge1}:
   q_a(c)=\sum_{m\ge1}6^{am}
      (|c_m^+|+|c_m^-|)<\infty
   \text{ for every }0<a<1\right\}.
\tag{25}
\]

The same weight-ratio proof as (23) makes this a nuclear Fréchet space:
for \(0<a<b<1\),

\[
                         \sum_{m\ge1}6^{-(b-a)m}<\infty.
\tag{26}
\]

For a real horizontal character \(\chi_\delta([u])=u^\delta\), evaluation of (24) is

\[
 V_6(\delta)=
 \left(
   \left(6^{-m(1-\delta)}\right)_{m\ge1},
   \left(-6^{-m(1+\delta)}\right)_{m\ge1}
 \right).
\tag{27}
\]

### Theorem 7.1 — exact open-strip admission

\[
 \boxed{
 V_6(\delta)\in
   (\ell^1\cap\ell^2)\oplus(\ell^1\cap\ell^2)
   \Longleftrightarrow |\delta|<1.}
\tag{28}
\]

For \(|\delta|<1\), character evaluation
\[
 \operatorname{Ev}_\delta:
   \mathcal K_{\Gamma,6}\longrightarrow
   \ell^1\oplus\ell^1
   \hookrightarrow\ell^2\oplus\ell^2
\tag{29}
\]
is continuous.

### Proof

The forward sequence in (27) is geometric with ratio \(6^{-(1-\delta)}\); it lies in
\(\ell^1\), equivalently in \(\ell^2\), exactly when \(\delta<1\). The reciprocal sequence has
ratio \(6^{-(1+\delta)}\), so it is admitted exactly when \(\delta>-1\). This proves (28).

For continuity, choose \(a\) with \(|\delta|<a<1\). For
\(c\in\mathcal K_{\Gamma,6}\),

\[
\begin{aligned}
 \|\operatorname{Ev}_\delta(c)\|_{\ell^1\oplus\ell^1}
 &\le \sum_m6^{|\delta|m}(|c_m^+|+|c_m^-|)\\
 &\le q_a(c).
\end{aligned}
\]

∎

Let reflection on the two slots be

\[
                         R(a,b)=(-b,-a).
\tag{30}
\]

Then

\[
                         R V_6(\delta)=V_6(-\delta).
\tag{31}
\]

The physical oriented reader is the codiagonal

\[
 \operatorname{OddRead}(a,b)_m=a_m+b_m.
\tag{32}
\]

It gives

\[
 \operatorname{OddRead}(V_6(\delta))_m
   =6^{-m}\left(6^{m\delta}-6^{-m\delta}\right).
\tag{33}
\]

Consequently

\[
 \operatorname{OddRead}(V_6(\delta))=0
       \Longleftrightarrow\delta=0,
\tag{34}
\]

and its \(m=1\) coordinate is \(6^{-1}K_6(\delta)\). Thus admission is unconditional on every
nontrivial Xi divisor fibre, while annihilation remains exactly the critical-line statement.

Tensoring (24) with the canonical two-dimensional Laurent-germ pair

\[
 \left(B_6(s),-\frac{A(s)}{A(1-s)}B_6(1-s)\right)
\tag{35}
\]

preserves (28): at any fixed nontrivial divisor germ, both germ factors span a finite-dimensional
principal-part space, and the coefficient sequences remain in \(\ell^1\cap\ell^2\). The scalar
functional-equation codiagonal cancels their poles, while the resolved orientation codiagonal is
(33). This constructs the source-first mixed **coefficient** admission of the actual odd pole
pair. It does not construct the Rost--Schmid-to-Meyer chain differential or prove cyclicity of the
fixed physical reader.

The source-normalized strict refinement is now classified in
deninger-gamma-six-critical-edge-coface-rigidity.md. The literal \(n=6\) Möbius atom forces
tensor-square edge \(6^{-m}\). In the resulting projective Köthe domain, the forward slot is
admitted exactly for \(\delta\le0\), the reciprocal slot exactly for \(\delta\ge0\), and both
exactly for \(\delta=0\). Thus the remaining problem is not to guess a stricter topology. It is
to derive, from the completed Green chain before divisor selection, simultaneous landing in both
of those source-forced slots.

## 8. Exact no-go for denominator repair

Let \(R\) denote reflection exchanging the two Gamma-six normal orientations, and let
\(\operatorname{Odd}=(1-R)/2\). For any placewise linear transport \(F_\ell\) which factors
through the common-pole normalized residue (11), Theorems 4.1--4.2 give

\[
 \operatorname{Odd}\,
 F_\ell\bigl(\text{Gamma-six normal cell at }\ell\bigr)=0.
\tag{36}
\]

This remains true after arbitrary direct sums, completions, weights, Frobenius traces, and
continuous packet maps. Therefore no denominator-place construction functorial in the honest
common-pole residue can cancel the nonzero reflection-odd archimedean coefficient

\[
                         6^{m\delta}-6^{-m\delta}.
\tag{37}
\]

Any proposed repair using \([\bar6]-[1]\), a chosen primitive packet, or a signed coefficient
proportional to (37) must prove a new source differential connecting that extra packet to the
normal cell. Without such a theorem it is coefficient fitting.

This is the positive/no-go split:

- **positive survivor:** a nonzero, Frobenius-fixed, cofinally mixed-admissible rational-Witt
  boundary layer \(\mathcal E_6\);
- **rigidity:** that layer is canonically reflection-even and annihilated by every resolved odd
  reader;
- **remaining core:** signed relative chain descent of the forward/opposite-pole pair on the
  reduced odd source, not construction or weighting of denominator packets.

The full honest place set is

\[
 \{\infty,2,3,5\}\cup\{\ell:\ell\mid1+6^m
       \text{ for some }m\}.
\tag{38}
\]

Here \(5\) belongs to the finite correction defining \(B_6\), while the denominator set belongs
to the pre-normal Steinberg cell. After source-resolved reflection splitting, the denominator
summand lies in the even sector and the RH-bearing odd square still involves the fixed
Gamma/Burnol/BV landing.

## 9. Heavy conjecture audit

1. **Conjecture:** the honest Gamma-six source has only normalized \(\infty,2,3\) support.
   **Falsified.** Denominator primes dividing \(1+6^m\) are infinite.
2. **Conjecture:** tame and Kummer invisibility mean denominator packet vanishing.
   **Falsified.** The exact residue \(\varepsilon_\ell=[-1]-[1]\) is a nonzero
   Frobenius-fixed rational-Witt packet.
3. **Conjecture:** the denominator packet carries the reflection-odd Gamma anomaly.
   **Falsified sharply.** Forward and reciprocal residues are identical; their odd difference is
   zero.
4. **Conjecture:** a larger packet \([\bar6]-[1]\) repairs this collapse automatically.
   **Rejected as coefficient fitting.** It is source-available but is not the residue of the
   oriented normal; a new signed relative differential is required to connect it.
5. **Conjecture:** cofinal denominator support creates a remaining topology obstruction.
   **Falsified constructively.** Tensor-square grade \(6^{-m}\) gives the mixed admission (20)--(23).
6. **Conjecture:** the odd forward/opposite-pole pair itself has no source-first common mixed
   coefficient domain. **Falsified sharply.** Its tensor-square grade has the exact admission
   domain \(|\delta|<1\), equation (28), and retains \(K_6\) in grade one.
7. **Conjecture:** this admission supplies the missing zero. **Falsified transparently.**
   Its actual oriented codiagonal is (33), which vanishes exactly at \(\delta=0\).

## 10. Novelty and hostile audit

- Infinitude of prime divisors, tame symbols, finite cyclic characters, and Köthe nuclearity are
  classical ingredients; no independent novelty is claimed for them.
- Project-specific new knowledge is the exact common-pole residue calculation (13)--(17) for the
  Gamma-six normal and its consequence: the hidden cyclotomic denominator layer is nonzero but
  purely reflection-even.
- The exact open-strip coefficient admission (24)--(35) is source-derived from the two actual
  normal orientations and the tensor-square complete-tail scale; it is not the rejected
  denominator coupling.
- The paper explicitly retracts the tempting stronger construction
  \((6^{m\delta}-6^{-m\delta})([\bar6]-[1])\): no source theorem derived that coefficient-packet
  coupling.
- No Xi-zero location, RH premise, positivity assumption, numerical experiment, new reader, or
  quotient defined by the desired kernel is used.

## 11. Formalization certificate

- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/DeningerGammaSixCyclotomicDenominatorAdmission.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Closed capstone:** `gammaSixCyclotomicDenominatorAdmission_closed`
- **Denominator infinitude:** `gammaSixFermatDenominator_coprime`,
  `gammaSixDenominatorPrime_injective`, and `gammaSixDenominatorPlaceSet_infinite` use the explicit
  source family (m_n=2^n).  Pairwise coprimality of (6^{2^n}+1) yields distinct least prime
  divisors and strengthens the recursive cofinal construction needed in Section 2 without a
  primitive-divisor theorem.
- **Local arithmetic:** `gammaSix_denominatorExactValuations` and
  `gammaSix_denominatorExactTameKummer` prove the two exact valuations, unit ratio, trivial tame
  symbol, and zero (p)-adic logarithmic norm at every denominator prime.
- **Actual common-pole residue:** `gammaSix_forward_commonPoleResidue_eq_epsilon`,
  `gammaSix_reciprocal_commonPoleResidue_eq_epsilon`, and
  `gammaSix_denominator_orientationCollapse` prove the forward/reciprocal equality and exact odd
  collapse in the concrete group algebra `MonoidAlgebra ℂ (ZMod p)ˣ`.
- **Canonical rational-Witt survivor:** `gammaSixParityWittResidue_ne_zero`,
  `gammaSixParityWittResidue_evaluation`, and
  `gammaSixPrimeRationalWittParityResidue_frobenius_fixed` prove nonvanishing, evaluation (-2),
  and Frobenius fixation.  `gammaSixParityResidueInclusion_maps_epsilon` constructs the canonical
  order-two packet embedding and proves that its parity class maps to the actual denominator
  residue ([-1]-[1]), rather than merely matching it by an abstract coefficient.
- **Cofinal and mixed admission:** `gammaSixEvenDenominatorPacket_mixed_admission`,
  `gammaSixMixedKotheData_isNuclear`, `gammaSixMixedKothe_mem_iff`, and
  `gammaSixMixedHorizontalEvaluation_continuityGrade` construct the cofinal packet, nuclear
  two-slot Köthe carrier, exact carrier characterization, and bounded horizontal evaluation.
- **Sharp strip and rigidity:** `gammaSixMixedEvaluatedPair_admission_iff`,
  `gammaSixMixedReflection_evaluatedPair`, and
  `gammaSixMixedOddRead_evaluatedPair_eq_zero_iff` prove exact ℓ¹/ℓ² admission iff
  |δ|<1, the reflection law, and odd-reader vanishing iff δ=0.
- **Functorial no-go:** `gammaSixCommonPole_factor_odd_zero` proves collapse after every additive
  transport factoring through the honest common-pole residue.
- **Verification:** direct source check with
  `lake env lean GaloisForLFunctions/RHTower/DeningerGammaSixCyclotomicDenominatorAdmission.lean`
  and exact module audit with
  `lake build GaloisForLFunctions.RHTower.DeningerGammaSixCyclotomicDenominatorAdmission` both
  pass.  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for all audited
  headline theorems.  Source contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- **Scope:** `[NOT RH]`.  Formalization closes denominator classification and admission; it does
  not supply completed Green landing in both critical-edge slots, strict Rost--Schmid-to-Meyer
  descent, or cyclicity of the fixed physical reader.

## 12. Frontier ledger

- [x] identify full pre-normal denominator support
- [x] prove denominator places form an infinite cofinal family
- [x] prove tame/Kummer invisibility
- [x] compute exact nonzero common-pole rational-Witt residue
- [x] prove forward and reciprocal denominator residues coincide
- [x] prove denominator layer is reflection-even and odd-reader invisible
- [x] construct nuclear mixed admission of the cofinal even layer
- [x] rule out denominator packets as automatic signed counterterm
- [x] construct sharp mixed coefficient admission of the reduced odd pole pair on \(|\delta|<1\)
- [x] classify the source-forced critical-edge strict domain and its exact zero locus
- [x] rule out adjacent-grade, finite-convolution, and Euler-depletion shortcuts
- [ ] prove source-derived completed Green landing in both critical-edge slots
- [ ] construct strict Rost--Schmid-to-Meyer chain differential on that admitted odd pair
- [ ] prove fixed Burnol/Deninger reader cyclic on that transported odd boundary
