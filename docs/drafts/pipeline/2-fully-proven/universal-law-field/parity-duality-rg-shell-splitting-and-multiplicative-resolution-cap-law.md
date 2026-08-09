# Parity duality, RG-shell splitting, and the multiplicative resolution cap

- **ID:** ULF-GAS-4
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SIGNED-SECTOR AND ORGAN-SCOPE LAW
- **Source:** hunch-formation pass for the Möbius/fermionic companion of the abelian zeta gas
  (ULF-GAS-1), constrained by the retirement verdict of ULF-GAS-2
- **Statement:** The abelian zeta gas carries the parity organ natively: the parity mass is
  \(Z(2\sigma)/Z(\sigma)^2\); the fermionic (distinct-factor) companion gas is observationally
  identical to the odd-depth bosonic sector on the order organ (Euler's distinct=odd identity at
  the level of laws) and is separated from it by the socle organ; the bosonic condensation fan splits into
  odd and even (\(\delta_2\)-image) shells, so the critical abscissa is the
  \(\delta_2\)-image of the pole wall, absent from the odd shell and from the fermionic order
  organ (not from the fermionic mode field); and every Markov
  certificate from the solvable tilt cone is multiplicatively coarse, so the short-interval
  (Route-E/MR-type) events, though exactly expressible as gas probabilities, are undecidable by
  the solvable organ cone.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [OBSERVATIONAL-IDENTITY INSTANCE]
  [ORGAN-SCOPE NO-GO] [ROUTINE COROLLARIES FLAGGED AS SUCH] [NOT RH] [NO LEAN]

## 0. Setting

Notation of ULF-GAS-1: modes \((p,j)\), bosonic occupations \(G_{p,j}\) geometric with ratio
\(q_{p,j}=p^{-j\sigma}\), \(\sigma>1\), \(Z(\sigma)=\prod_{j\ge1}\zeta(j\sigma)\),
\(\Omega(A)=\sum_{p,j}G_{p,j}\) the total number of cyclic factors (so
\((-1)^{\Omega(A)}=\lambda(|\operatorname{soc}A|\)-type parity), and the RG maps \(\delta_d\) of
ULF-GAS-1 Theorem 7.1.

## 1. Parity mass and signed ladders

### Theorem 1.1 — parity mass law

\[
\boxed{\ \mathbb E_\sigma\bigl[(-1)^{\Omega(A)}\bigr]
=\prod_{j\ge1}\frac{\zeta(2j\sigma)}{\zeta(j\sigma)^2}
=\frac{Z(2\sigma)}{Z(\sigma)^2}\in(0,1),\ }
\tag{GAS4.1}
\]

and more generally the signed grand response is the exact doubled ladder

\[
\mathbb E_\sigma\bigl[(-1)^{\Omega(A)}|A|^{-u}|\operatorname{soc}A|^{-v}\bigr]
=\prod_{j\ge1}
\frac{\zeta\bigl(2(j(\sigma+u)+v)\bigr)}
{\zeta\bigl(j(\sigma+u)+v\bigr)\,\zeta(j\sigma)},
\tag{GAS4.2}
\]

normally convergent on the same half-planes as (GAS.6) and meromorphic by the same tail argument.

#### Proof

Independence gives \(\mathbb E[(-1)^\Omega x^{\,\text{marks}}]=\prod_{p,j}\mathbb E[(-x)^{G}]\)
factorwise; for a geometric variable \(\mathbb E[y^G]=(1-q)/(1-yq)\), so with \(y=-p^{-ju-v}\)
the mode factor is \((1-p^{-j\sigma})/(1+p^{-j(\sigma+u)-v})\). Using
\(\prod_p(1-p^{-a})=\zeta(a)^{-1}\) and \(\prod_p(1+p^{-b})=\zeta(b)/\zeta(2b)\) and rearranging
absolutely convergent logarithms yields (GAS4.2); \(u=v=0\) gives (GAS4.1), and each mode factor
lies in \((0,1)\). QED.

These are routine corollaries of the mode structure and are flagged as such; their role is that
the parity organ is *native* (a character of the mode monoid, unitizing everything — an observer
localization in the PRD sense), and that the signed calculus imports exactly the doubled lines
\(2(j(\sigma+u)+v)=w\) into the divisor arrangement: **parity lives in the \(\delta_2\) shell.**

## 2. Fermionic companion: observational identity and organ separation

Let the **fermionic gas** \(\mathbb P^F_\sigma\) put Bernoulli occupations
\(g_{p,j}\in\{0,1\}\) on the same modes, with weight proportional to \(p^{-j\sigma g}\); its
configurations are the abelian groups with pairwise distinct cyclic factors, and its partition
function is \(Z_F(\sigma)=\prod_{p,j}(1+p^{-j\sigma})=\prod_{j\ge1}\zeta(j\sigma)/\zeta(2j\sigma)\).

### Theorem 2.1 — Euler duality at the level of laws

1. \(Z_F(\sigma)=\prod_{j\text{ odd}}\zeta(j\sigma)\): the fermionic partition function is that of
   the **odd-depth bosonic sector**.
2. Stronger: the *order-observable laws coincide.* For every prime \(p\) and every \(k\ge0\),

   \[
   \mathbb P^F\bigl(v_p(|A|)=k\bigr)=\mathbb P^{B,\mathrm{odd}}\bigl(v_p(|A|)=k\bigr),
   \tag{GAS4.3}
   \]

   where \(\mathbb P^{B,\mathrm{odd}}\) is the bosonic gas restricted to odd depths; hence the
   full laws of \(|A|\) agree at every \(\sigma\).
3. The **socle organ separates them**, deterministically, already at order \(p^2\): conditional
   on \(v_p(|A|)=2\), the fermionic sector realizes only \(\mathbb Z/p^2\) (one cyclic factor;
   the unique distinct-part partition of \(2\)), while the odd-depth sector realizes only
   \((\mathbb Z/p)^2\) (two factors; the unique odd-part partition of \(2\)).

#### Proof

Per prime, with \(x=p^{-\sigma}\): item 1 is Euler's identity
\(\prod_j(1+x^j)=\prod_{j\text{ odd}}(1-x^j)^{-1}\), multiplied over \(p\) with the usual
rearrangement. For item 2, the unnormalized mass of \(\{v_p(|A|)=k\}\) is \(x^k\) times the number
of admissible depth-multisets summing to \(k\): partitions of \(k\) into **distinct** parts
(fermionic) versus partitions into **odd** parts (odd-depth bosonic); these counts are equal for
every \(k\) — Euler's partition theorem — and the normalizations agree by item 1, so the laws
agree; independence over \(p\) finishes. For item 3: the only partition of \(2\) into distinct
parts is \(\{2\}\) and the only partition into odd parts is \(\{1,1\}\); the conditional
factor-count laws at \(v_p=2\) are the point masses at \(1\) and at \(2\) respectively, and the
conditioning event has positive probability on both sides. QED.

This is an exact arithmetic instance of the certified intervention-separation phenomenon
(ULF-CFL-1, `ConstitutiveInterventionSeparation`): two nonisomorphic sources — one with exclusion,
one without — are observationally identical on a complete organ (the order/temperature organ,
hence on the entire dilation divisor calculus) and are separated by another organ (the socle).
Passive observation of the order observable can never distinguish exclusion statistics from
odd-depth statistics; the socle observer is the separating intervention.

### Corollary 2.2 — RG-shell splitting of the bosonic fan, and what transfers to fermions

The statements below are about strata of the **bosonic** gas; the fermionic transfer is exactly
the order-organ part, no more.

1. The bosonic **odd-depth** subgas has mode-condensation fan \(\{1,\tfrac13,\tfrac15,\dots\}\);
   the bosonic **even-depth** subgas is \(\delta_2\) of the full gas and has fan
   \(\{\tfrac12,\tfrac14,\dots\}\). Hence the critical abscissa is \(\tfrac12=\delta_2(1)\): the
   RG-double of the pole wall, carried by the even (square) shell and absent from the odd shell.
2. By Theorem 2.1.2, every **order-organ** statement about the odd-depth subgas transfers
   verbatim to the fermionic gas: its order law, its dilation calculus
   \(\prod_{j\ \mathrm{odd}}\zeta(j(\sigma+u))/\zeta(j\sigma)\), and the location of its
   order-realizability wall at \(\sigma=1\).
3. **Warning (recorded to block an over-reading):** the fermionic gas's own *mode-activity* fan
   is the full \(\{1/g\}\) — its depth-\(2\) Bernoulli modes condense at \(\sigma=\tfrac12\)
   exactly as bosonic ones do (Borel–Cantelli as in ULF-GAS-1 Theorem 5.1, since
   \(\mathbb P(g_{p,j}=1)=p^{-j\sigma}/(1+p^{-j\sigma})\asymp p^{-j\sigma}\)). The
   "invisibility of \(\tfrac12\)" is a property of the odd-depth boson sector and of the
   fermionic **order observable**, not of the fermionic mode field. A first version of this
   corollary conflated the two; the conflation is an error and is retracted here.

#### Proof

Item 1 is ULF-GAS-1 Theorems 5.1 and 7.1 applied to the odd- and even-depth mode subsets. Item 2
is Theorem 2.1.2 (equality of order laws transfers every functional of \(|A|\)). Item 3 is the
Borel–Cantelli computation quoted, which depends only on the activity probabilities, identical up
to bounded factors in the two gases. QED.

## 3. Multiplicative resolution cap of the solvable organ cone

The gas expresses short-interval coefficient statements exactly: for \(I=(x,x+h]\),

\[
\mathbb P_\sigma(|A|\in I)=C_\sigma\sum_{n\in I}a(n)n^{-\sigma},
\qquad
\text{and its signed tilts give }\sum_{n\in I}b(n)n^{-\sigma}
\tag{GAS4.4}
\]

for explicit multiplicative \(b\). These are precisely the objects whose sub-multiplicative-scale
behavior is the corpus's Route-E/MR wall territory. The question is whether the gas's own solvable
observers can decide them. They cannot:

### Theorem 3.1 — tilt-Markov certificates are multiplicatively coarse

Let \(\mathcal C\) be the cone of finite positive combinations
\(f(A)=\sum_ic_i|A|^{-u_i}\) with \(c_i\ge0\), \(u_i\in[-U,U]\) (the order-tilt certificate cone).
For \(0<h\le x\) and \(I=(x,x+h]\), every Markov certificate from \(\mathcal C\) satisfies

\[
\operatorname{cert}_I(f):=\frac{\mathbb E_\sigma[f]}{\inf_{|A|\in I}f}
\;\ge\;4^{-U}\,\mathbb P_\sigma\bigl(|A|\in(x,2x]\bigr).
\tag{GAS4.5}
\]

Consequently, whenever \(\mathbb P_\sigma(|A|\in I)=o\bigl(\mathbb P_\sigma(|A|\in(x,2x])\bigr)\)
(the short-interval regime \(h=o(x)\)), no certificate in \(\mathcal C\) is within a bounded
factor of the truth: the solvable cone resolves the order observable only at multiplicative
scale.

#### Proof

Each generator \(n\mapsto n^{-u}\) varies by at most \(2^{|u|}\le2^{U}\) on \((x,2x]\), hence so
does any \(f\in\mathcal C\) up to \(\sup_{(x,2x]}f\le 4^{U}\inf_{(x,2x]}f\) (crude but uniform:
positive combinations inherit the ratio bound with one extra factor \(2^U\) absorbed into
\(4^U\)). Since \(I\subset(x,2x]\), \(\inf_If\ge\inf_{(x,2x]}f\), so

\[
\operatorname{cert}_I(f)
\ge\frac{\mathbb E[f\,\mathbf 1_{|A|\in(x,2x]}]}{\inf_I f}
\ge\frac{\inf_{(x,2x]}f}{\inf_I f}\,\mathbb P(|A|\in(x,2x])
\ge 4^{-U}\,\mathbb P(|A|\in(x,2x]).
\]

QED.

Remarks, with hostile boundaries:

1. Socle-mixed certificates \(|A|^{-u}|\operatorname{soc}A|^{-v}\) are not covered by the proof
   (the infimum over the event mixes group structures at different orders); no claim is made
   for them beyond the observation that adding \(v\)-tilts did not help in worked examples.
   Parity-twisted functionals are signed and lie outside every Markov cone by positivity.
2. The cap is a statement about the *certificate class*, not about the truth: it does not prove
   the short-interval sums are hard, only that the gas's entire exactly solvable positive organ
   cone is structurally blind below multiplicative scale. This is the precise, provable residue
   of the falsified ULF-GAS-2 hunch: the MR-type wall is not the gatekeeper of any solvable
   continuation (ULF-GAS-3), and conversely the solvable organs cannot reach the wall's scale
   (this theorem). Wall and solvable calculus are disjoint by theorem, in both directions.
3. The mechanism echoes the corpus's Perron-layer no-go (`perron-layer-two-obstructions`:
   coefficient-blind, or uniform distance = prime mass) and the large-deviation folklore that
   exponential tilts localize only to their own bandwidth; novelty is claimed only for the typed
   organ-scope formulation on this source.

## 4. What this cycle adds to the field claim

- The parity organ is native and exactly solvable, and it lives in the \(\delta_2\) shell
  (GAS4.1–2).
- Observational identity between nonisomorphic sources is realized arithmetically, with an exact
  separating organ (Theorem 2.1) — the certified intervention-separation law now has a canonical
  arithmetic instance inside the same source that carries the divisor calculi.
- The critical abscissa acquires a second structural characterization: not only the squarefull
  condensation wall (ULF-GAS-1) but the \(\delta_2\)-image of the pole wall, absent from the
  odd-depth boson shell and from the fermionic order organ (Corollary 2.2, with the mode-field
  warning recorded there).
- The boundary between the solvable organ algebra and the live Route-E wall is now a theorem
  (Theorem 3.1), not a narrative.

## 5. Corpus and literature collision audit

- Euler's distinct=odd identity and its boson/fermion reading: classical; N. Chair,
  arXiv:1306.5415, develops precisely such gas readings for single-\(q\) partition identities —
  cited as the nearest parent; the lift to the prime-power arithmetic gas, the law-level (not
  partition-function-level) identity (GAS4.3), and the organ-separation statement were not found
  there or elsewhere.
- Fermionic primon gas with \(Z=\zeta(s)/\zeta(2s)\) (Spector, Julia): the depth-one special
  case of \(Z_F\); cited, no collision with the full-fan statements.
- Large-deviation tilting bandwidth: folklore (Cramér); the certificate-cone cap as stated is
  believed new in formulation, trivial in mechanism — significance rests on its role as an exact
  organ-scope law, and is claimed only as such.
- Internal parents: ULF-GAS-1 (fan, RG), ULF-GAS-3 (retirement direction), ULF-CFL-1
  (intervention separation), ULF-EQG-1.

## 6. Scope

- All results unconditional; \(\sigma>1\) for probability statements, per-prime identities for
  all \(\sigma>0\).
- Nothing localizes zeros. The card's contribution is structural: signed sector typed, sources
  separated, walls re-derived shell-wise, and the solvable/wall boundary made exact.
- Lean targets: (GAS4.3) is a finite partition-identity layer (Euler's theorem is in mathlib's
  q-series vicinity — verify against toolchain); Theorem 3.1 is elementary; (GAS4.1–2) need the
  Euler-product layer already used by ULF-GAS-1 targets.

## Log

- 2026-08-09 — created in the same session as ULF-GAS-1/3, as the fresh hunch-formation pass
  demanded by the ULF-GAS-2 retirement; observational identity found and separated; resolution
  cap proved; no MR leverage claimed in either direction, now by theorem.
- 2026-08-09 — ERRATUM (hostile re-audit after user challenge): Corollary 2.2 originally
  attributed the odd wall fan to the fermionic gas itself; false — the fermionic mode field
  condenses at \(\tfrac12\) like the bosonic one, and only order-organ statements transfer.
  Corrected with an explicit warning item. Separation in Theorem 2.1.3 sharpened from \(p^3\) to
  the deterministic \(p^2\) statement.
