# Rational-Witt affine packet gauge limit

- **ID:** `deninger-rational-witt-packet-gauge-limit`
- **Stage:** 3-formalized
- **Type:** GLOBAL SOURCE-TO-PACKET TORSOR THEOREM
- **Label:** `DAC_DENINGER_WRAT_PACKET_GAUGE_LIMIT`
- **Parent:** `deninger-rational-witt-packet-gauge-descent`
- **Scientific status:** `[FORMALIZED] [SOURCE-SPECIFIC SYNTHESIS; EXTERNAL PRIORITY UNVERIFIED]`
- **RH dependency:** closes canonical globalisation of finite rational-Witt packet gauges and
  transports full-support Haar `L²` to their affine limit.  Subsequent work now closes
  tensorized Calderón descent on this affine limit.  It does not yet construct the graded
  all-prime secondary attachment, Meyer comparison, closed middle boundaries, Hodge positivity,
  or Xi spectral theorem.

## 1. Open problem

Fix a rational prime \(p\).  For every prime-to-\(p\) finite Frobenius stage \(s\), put
\[
 Q_s=(\mathbb Z/n_s\mathbb Z)^\times/\langle p\rangle .
\]
For \(s\le t\), the rational-Witt primitive-root choices force the affine transition
\[
 \kappa_{s,t}(q)=g_{s,t}\rho_{s,t}(q),                 \tag{1}
\]
where \(\rho_{s,t}:Q_t\to Q_s\) is canonical quotient reduction and
\[
 g_{s,t}=[a_{s,t}]\in Q_s .
\]
The preceding theorem proves
\[
 \kappa_{r,s}\kappa_{s,t}=\kappa_{r,t},\qquad
 \kappa_{s,s}=\operatorname{id}.                       \tag{2}
\]

Because of the translation \(g_{s,t}\), the maps \(\kappa_{s,t}\) are not homomorphisms.  Their
inverse limit therefore cannot honestly be declared a profinite group.  The missing global
question was whether it contains extra states, loses states, or is an affine form of Deninger's
actual packet.

## 2. Canonical transition law for the actual packet

Let
\[
 P_p=\left(\prod_{\ell\ne p}\mathbb Z_\ell^\times\right)/
       \overline{\langle p\rangle}
\]
be the literal Deninger packet.  Existing reductions
\[
 r_s:P_p\longrightarrow Q_s
\]
were separately constructed by prime-power coordinates and CRT.  The corpus had proved
surjectivity, continuity, and joint injectivity, but only the weaker implication
\[
 r_t(x)=r_t(y)\Longrightarrow r_s(x)=r_s(y).
\]
It then defined a transition \(Q_t\to Q_s\) by choosing a lift through \(r_t\).  Equality with the
canonical map \(\rho_{s,t}\) was open.

### Canonical CRT naturality

`[PROVED HERE]`
\[
 \boxed{\qquad
 \rho_{s,t}(r_t(x))=r_s(x)
 \qquad(s\le t,\ x\in P_p).
 \qquad}                                                 \tag{3}
\]

The proof is at raw unit level.  A prime factor \(q\mid n_s\) is refined to the same prime factor
of \(n_t\).  Its factorization exponent is monotone.  The two typed away-prime coordinates are
identified, their \(q\)-power reductions commute by the \(\ell\)-adic transition theorem, and
the unequal CRT transport square commutes because the relevant `ZMod` ring homomorphism is
unique.  Equality of all CRT components gives `(3)`.

Consequently the old choice-defined quotient factor is extensionally the canonical arithmetic
map:
\[
 \boxed{\qquad
 \operatorname{factor}_{s,t}=\rho_{s,t}.
 \qquad}                                                 \tag{4}
\]

## 3. Actual packet equals the standard finite inverse limit

Define
\[
 L_p=\left\{(x_s)_s\in\prod_sQ_s:
          \rho_{s,t}(x_t)=x_s\ \text{for every }s\le t\right\}. \tag{5}
\]
Equation `(3)` gives a continuous homomorphism
\[
 R:P_p\longrightarrow L_p,\qquad R(x)=(r_s(x))_s.       \tag{6}
\]
Joint injectivity of the \(r_s\) makes \(R\) injective.

For surjectivity, fix \(y=(y_s)\in L_p\) and consider the closed fibres
\[
 C_s=\{x\in P_p:r_s(x)=y_s\}.                            \tag{7}
\]
Each \(C_s\) is nonempty by finite-stage surjectivity.  Given \(s,t\), choose a common upper stage
\(u\).  Equations `(3)` and `(5)` imply
\[
 C_u\subset C_s\cap C_t.                                 \tag{8}
\]
The \(C_s\) are therefore a directed family of nonempty closed subsets of compact \(P_p\).
Their total intersection is nonempty, and any point in it maps to \(y\).  Thus \(R\) is a
continuous bijection from compact \(P_p\) to Hausdorff \(L_p\), hence
\[
 \boxed{\qquad P_p\cong_{\mathrm{homeo}}L_p.\qquad}      \tag{9}
\]

## 4. Affine gauge limit

Define the actual rational-Witt gauge limit
\[
 A_p=\left\{(a_s)_s\in\prod_sQ_s:
          \kappa_{s,t}(a_t)=a_s\ \text{for every }s\le t\right\}. \tag{10}
\]
Strict composition `(2)` makes \(Q_s,\kappa_{s,t}\) a finite inverse system.  Every \(Q_s\) is
finite and nonempty, so the finite cofiltered-section theorem gives
\[
 A_p\ne\varnothing.                                      \tag{11}
\]

No group law is imposed on \(A_p\).

## 5. Torsor classification

For \(a\in A_p\) and \(x\in L_p\), define coordinatewise
\[
 (a\cdot x)_s=a_sx_s.                                    \tag{12}
\]
Then
\[
\begin{aligned}
 \kappa_{s,t}(a_tx_t)
 &=g_{s,t}\rho_{s,t}(a_t)\rho_{s,t}(x_t)\\
 &=a_sx_s,
\end{aligned}
\]
so \(a\cdot x\in A_p\).

For \(a,b\in A_p\), define
\[
 (a\backslash b)_s=a_s^{-1}b_s.                          \tag{13}
\]
The common affine translation cancels:
\[
\begin{aligned}
 \rho_{s,t}(a_t^{-1}b_t)
 &=\rho_{s,t}(a_t)^{-1}\rho_{s,t}(b_t)\\
 &=(g_{s,t}^{-1}a_s)^{-1}(g_{s,t}^{-1}b_s)\\
 &=a_s^{-1}b_s.
\end{aligned}
\]
Hence \(a\backslash b\in L_p\), and
\[
 a\cdot(a\backslash b)=b,\qquad
 a\backslash(a\cdot x)=x.                                \tag{14}
\]

Therefore:
\[
 \boxed{\quad
 \text{\(L_p\) acts simply transitively on \(A_p\).}
 \quad}                                                   \tag{15}
\]
Equivalently, \(A_p\) is an \(L_p\)-torsor.  Choosing any \(a_0\in A_p\) gives
\[
 L_p\xrightarrow{\sim}A_p,\qquad x\longmapsto a_0\cdot x, \tag{16}
\]
with inverse \(a\mapsto a_0\backslash a\).  Both maps are continuous coordinatewise, so `(9)`
and `(16)` yield
\[
 \boxed{\qquad P_p\cong_{\mathrm{homeo}}A_p.\qquad}       \tag{17}
\]
The trivialization uses a coherent point; the affine system itself is not falsely presented as
a group with a distinguished identity.

## 6. Haar and `L²` transport

Let \(h_p:P_p\to A_p\) be the homeomorphism `(17)` obtained after choosing one coherent point.
Transport normalized Haar probability:
\[
 \mu^{\mathrm{gauge}}_p=(h_p)_*\mu^{\mathrm{Haar}}_p.      \tag{18}
\]
It is a probability measure, positive on every nonempty open set.  Hence
\[
 L^2(A_p,\mu^{\mathrm{gauge}}_p)
\]
is a full packet fibre, and the canonical map
\[
 C(A_p,\mathbb R)\longrightarrow
 L^2(A_p,\mu^{\mathrm{gauge}}_p)                           \tag{19}
\]
is injective.  No continuous affine packet mode is lost.

## 7. RH dependency consequence

Closed here:

1. actual packet reductions commute with canonical finite transitions;
2. the actual Deninger packet is the standard finite inverse limit;
3. the rational-Witt gauge system has a nonempty global affine limit;
4. that limit is a torsor under, and homeomorphic to, the actual packet;
5. normalized full-support Haar `L²` transports to the affine limit.

This removes the global packet ambiguity from the source-to-packet coefficient chain.

The strengthened source-horizon theorem rules out complete orientation transport by a closable
single-valued map in the canonical collapsing source topology and also rules out its replacement
by an ordinary ungraded closed relation: such a relation is
\(\operatorname{dom}\mathcal R\times\mathbb C^{\mathbb N}\). It does not invalidate `(17)`:
the compact packet topology here is a different object.

The tensorized first-suspension cross-effect has since been descended to the affine gauge limit.
Finite-stage functions, their complex Haar `L²` vectors, first-suspension vectors, and tensor
cross-effects are literally invariant under every forced gauge refinement. Every nonzero finite
packet coefficient has one cofinal arithmetic-Frobenius-fixed Wrat witness.

Exact next frontier:

1. construct a grade-preserving all-prime secondary attachment before closure;
2. equip it with a non-product topology retaining rational-Witt, suspension, and prime
   graph-energy grades;
3. identify its arithmetic differential and prove its closed radical is exactly the actual
   middle-boundary space;
4. only then transport cup/Hodge positivity and Xi spectral inclusion.

## 8. Hostile theatre audit

- **Not a renamed profinite limit theorem.**  The compactness argument `(9)` is standard
  infrastructure.  New source-facing content is that the independently constructed CRT packet
  reductions satisfy the exact canonical transition law `(3)`, allowing them to be used at all.
- **Not a fake group structure.**  The gauge transition is affine.  \(A_p\) is formalized as a
  subtype of coherent families, and only the simply transitive \(L_p\)-action is asserted.
- **Not merely nonemptiness.**  Equations `(12)`--`(15)` classify every pair of affine coherent
  packets by a unique actual packet displacement.
- **Not RH closure.**  No Meyer attachment, boundary theorem, Hodge theorem, or zero exclusion is
  claimed.
- **No RH premise.**  The proof uses finite Frobenius quotients, CRT, compactness, strict gauge
  composition, and Haar transport.

## 9. Novelty audit

General facts used without novelty credit:

- inverse limits of nonempty finite systems are nonempty;
- a continuous bijection from compact to Hausdorff is a homeomorphism;
- affine inverse systems whose translations share one linear part form torsors when coherent
  points exist;
- Haar probability transports through a homeomorphism.

Source-specific candidate new synthesis:

- exact CRT naturality `(3)` for this literal packet construction;
- equality `(4)` between the choice-defined factor and the canonical Frobenius transition;
- classification of the rational-Witt forced gauge limit as a torsor under Deninger's actual
  packet;
- faithful Haar `L²` transport matching the finite rational-Witt coefficient functor.

Repository search found finite reductions, joint injectivity, a choice-defined factor, standard
finite packet pullbacks, and fixed-stage Haar fibres.  It found no canonical transition theorem,
no actual packet inverse-limit equivalence, and no affine rational-Witt gauge torsor.  External
priority remains provisional.

## 10. Gates

- [x] canonical raw CRT transition law
- [x] canonical quotient transition law
- [x] actual packet inverse-limit homeomorphism
- [x] affine gauge limit nonempty
- [x] simply transitive actual-packet action
- [x] affine-limit homeomorphism
- [x] full-support Haar probability transport
- [x] faithful continuous-to-Haar-`L²` channel
- [x] tensorized Calderón cross-effect on affine limit
- [ ] graded all-prime secondary attachment and closed middle boundary

## 11. Lean realization

Modules:

- `formal/GaloisForLFunctions/RHTower/DeningerPrimeFiniteCyclotomicTransitionNaturality.lean`;
- `formal/GaloisForLFunctions/RHTower/DeningerPrimeFinitePacketInverseLimit.lean`;
- `formal/GaloisForLFunctions/RHTower/DeningerRationalWittPacketGaugeLimit.lean`.

Formal capstones:

- `deningerPrimeFiniteStageReduction_transition`;
- `deningerPrimeFiniteStageQuotientReduction_transition`;
- `deningerPrimeFiniteStageQuotientFactor_eq_canonical`;
- `deningerPrimePacketToFiniteLimit_surjective`;
- `deningerPrimePacketFiniteLimitHomeomorph`;
- `deningerPrimeFinitePacketGaugeLimit_nonempty`;
- `deningerPrimeFinitePacketGaugeLimit_simplyTransitive`;
- `deningerPrimePacketGaugeLimitHomeomorph`;
- `deningerPrimeFinitePacketGaugeContinuousToHaarL2_injective`.

Verification:

- all three modules pass direct `lake env lean <file>`;
- targeted builds pass for all three module dependencies, including final target
  `GaloisForLFunctions.RHTower.DeningerRationalWittPacketGaugeLimit`;
- axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- all modules are wired into `GaloisForLFunctions.RHTower`.
