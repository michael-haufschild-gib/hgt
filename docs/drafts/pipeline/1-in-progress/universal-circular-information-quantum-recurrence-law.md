# Universal circular-information law of quantum recurrence

- **ID:** `universal-circular-information-quantum-recurrence-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL THEOREM CANDIDATE / FINITE-AND-COUNTABLE
  PROJECTIVE RECURRENCE / EXACT TARGET INFORMATION / MINIMAX CLOCK
- **Scientific status:** `[UNCONDITIONAL PAPER THEOREM V1]`
  `[SPECIALIST FALSITY ATTACK PASSED 2026-07-29]`
  `[BRIDGE] [REJECTED AS NATURE MASTER 2026-07-29]`
  `[LEAN NOT AUTHORIZED]`
- **Supersedes as master candidate:**
  `maximal-stationary-quantum-recurrence-law.md`
- **One-sentence law:** For every finite or countably infinite pure-point
  quantum spectrum, one intrinsic circular phase-space information controls
  both exact return rarity and the least multiplicative deadline that
  guarantees a return after every observed exit.

## 0. Master-candidate rejection

This theorem is broad but does not currently establish a new universal law
at the requested scientific level.

The decisive hostile objection is structural:

1. Haar union avoidance gives the information lower bound;
2. Ruzsa covering gives the deterministic upper bound;
3. Bohr almost periodicity gives the pure-point boundary;
4. the newly named circular information is defined from the exact volume
   needed by those parent arguments.

Joining these statements may be useful and the finite/countable theorem may
be new as an exact object. It does not constitute evidence of a new law of
nature. Sharpening constants, replacing a near-hit by an exit-conditioned
factor, or changing the entropy functional repairs scope and quality but
cannot manufacture conceptual novelty.

**Positive survivor.** `(URL)` remains a potentially publishable
mathematical-physics bridge and a reusable formal theorem. It is not the
master discovery and is not authorized for Lean until a later paper actually
needs it.

## 1. Exact domain and observable

Let \(J\) be nonempty and finite or countably infinite. Let
\[
 a_j\geq0,\qquad \sum_{j\in J}a_j=1,
\]
and discard zero-weight coordinates. On the product torus
\(\mathbb T^J\), with product Haar probability \(m_J\), define
\[
 M_a(z)=\sum_{j\in J}a_jz_j.                              \tag{1}
\]
The series converges uniformly because the weights are summable. For
\(0<\eta<1\), the projective fidelity target and its exact information are
\[
 A_a(\eta)=\{z:|M_a(z)|\geq1-\eta\},\qquad
 I_a(\eta)=-\log m_J(A_a(\eta)).                           \tag{2}
\]

For a pivot \(k\in J\), define the exact circular distortion
\[
 D_{a,k}(z)
  =\sum_{j\in J}a_j\bigl(1-\operatorname{Re}(z_j\bar z_k)\bigr),       \tag{3}
\]
its open circular ball
\[
 B_{a,k}(\delta)=\{z:D_{a,k}(z)<\delta\},                  \tag{4}
\]
the pivot-averaged volume
\[
 V_a(\delta)=\sum_{k\in J}a_k\,m_J(B_{a,k}(\delta)),        \tag{5}
\]
and circular recurrence information
\[
 C_a(\delta)=-\log V_a(\delta).                            \tag{6}
\]
Every \(V_a(\delta)\) is strictly positive for \(\delta>0\), including when
\(J\) is infinite.

For a phase packet \(\omega\in\mathbb T^J\), its tick-\(n\) return amplitude
is
\[
 R_a(n;\omega)=\left|\sum_ja_j\omega_j^n\right|.           \tag{7}
\]
Define the least spectrum-uniform recurrence deadline
\[
 T_a(\eta)=\min\left\{N\geq1:
   \forall\omega\in\mathbb T^J\ \exists\,1\leq n\leq N,\
  R_a(n;\omega)\geq1-\eta\right\}.                        \tag{8}
\]

Define the exit-conditioned universal recurrence factor
\[
\begin{split}
 \Gamma_a(\eta)=\min\{L\geq1:\;&
   \forall\omega\in\mathbb T^J\ \forall M\geq1,\\
 &R_a(M;\omega)<1-\eta\Longrightarrow
   \exists n,\ M<n\leq L(M+1),\
   R_a(n;\omega)\geq1-\eta\}.
\end{split}                                                \tag{8a}
\]
Thus \(\Gamma_a\) is not a near-hit clock. It is the least factor that works
after every witnessed exit, whatever the exit time.

## 2. Master universal law `[CONJECTURE]`

For every finite or countably infinite probability vector \(a\) and every
\(0<\eta<1\),
\[
\boxed{
 C_a(4\eta-2\eta^2)-2\log2
 \ \leq\ I_a(\eta)-\log2
 \ \leq\ \log\Gamma_a(\eta)
 \ \leq\ \log T_a(\eta)
 \ <\ C_a(\eta/16)+\log2 .
}                                                          \tag{URL}
\]

The leftmost inequality is allowed to become trivial at coarse fidelity.
The law is finite and informative at every positive resolution because
\(V_a(\delta)>0\). It has:

1. no finite-support premise;
2. no randomness premise on the actual quantum spectrum;
3. no rational-independence, genericity, or asymptotic premise;
4. no remainder proportional to support size;
5. exact quantification over every compatible phase packet and every
   witnessed exit time;
6. an exact physical realization by every pure-point unitary quantum
   survival amplitude, and a converse realization of every packet.

The change from the earlier Gaussian water law is structural. The invariant
is no longer a quadratic approximation plus an \(O(r)\) implementation
cost. It is the exact non-Gaussian circular phase-space volume seen by the
quantum fidelity target.

## 3. Target-volume proof

### 3.1 Inner inclusion

For every pivot \(k\),
\[
 \operatorname{Re}\bigl(\bar z_k M_a(z)\bigr)
 =1-D_{a,k}(z).                                           \tag{9}
\]
Hence
\[
 B_{a,k}(\eta)\subseteq A_a(\eta).                         \tag{10}
\]
Multiplying the indicators by \(a_k\), summing over \(k\), and integrating
gives
\[
 V_a(\eta)\leq m_J(A_a(\eta)),
\qquad
 I_a(\eta)\leq C_a(\eta).                                 \tag{11}
\]

### 3.2 Outer inclusion in averaged form

The exact projective variance identity is
\[
 \sum_ka_kD_{a,k}(z)=1-|M_a(z)|^2.                         \tag{12}
\]
On \(A_a(\eta)\), the right side is at most
\[
 \Delta_\eta=2\eta-\eta^2.                                \tag{13}
\]
Markov's inequality on the pivot probability vector \(a\) shows that at
least half of its mass lies on pivots satisfying
\[
 D_{a,k}(z)<2\Delta_\eta,                                  \tag{14}
\]
up to the harmless boundary convention obtained by replacing the radius
with an arbitrarily larger one and taking a monotone limit. Therefore
\[
 \mathbf1_{A_a(\eta)}(z)
 \leq2\sum_ka_k\mathbf1_{B_{a,k}(2\Delta_\eta)}(z).         \tag{15}
\]
Integration gives
\[
 m_J(A_a(\eta))
 \leq2V_a(4\eta-2\eta^2),                                 \tag{16}
\]
which is the leftmost inequality in `(URL)`.

More generally, for every \(c>1\),
\[
 C_a\!\left(c(2\eta-\eta^2)\right)
   -\log\frac{c}{c-1}
 \leq I_a(\eta).                                          \tag{17}
\]

## 4. Exact information lower bound on the universal clock

For every positive integer \(n\), coordinatewise multiplication
\[
 z\longmapsto z^n
\]
is a surjective continuous homomorphism of \(\mathbb T^J\), hence preserves
product Haar probability. For every \(N\),
\[
 m_J\!\left(\bigcup_{n=1}^N\{z:z^n\in A_a(\eta)\}\right)
 \leq N\,m_J(A_a(\eta)).                                  \tag{18}
\]
If \(N<m_J(A_a(\eta))^{-1}\), some phase packet has no return through
tick \(N\). Consequently
\[
 T_a(\eta)\geq
 \left\lceil m_J(A_a(\eta))^{-1}\right\rceil
\geq e^{I_a(\eta)},                                       \tag{19}
\]
which proves the middle inequality in `(URL)`.

This lower bound is adversarial but not probabilistic physics: Haar measure
is used only to prove existence of a compatible spectrum that defeats every
shorter universal deadline.

### 4.1 Exit-conditioned lower bound

Let \(L\) be a positive integer with
\[
 2L\,m_J(A_a(\eta))<1.                                    \tag{19a}
\]
Equation `(18)` with \(N=2L\) supplies a packet \(\omega\) for which no tick
\(1,\ldots,2L\) lies in the target. In particular it has exited at tick
\(M=1\), yet it does not return by
\[
 L(M+1)=2L.                                                \tag{19b}
\]
Therefore
\[
 \Gamma_a(\eta)\geq\frac{1}{2m_J(A_a(\eta))}
 =\frac12e^{I_a(\eta)},                                   \tag{19c}
\]
with integer rounding only strengthening the logarithmic inequality
\[
 I_a(\eta)-\log2\leq\log\Gamma_a(\eta).                   \tag{19d}
\]

## 5. Circular-information upper bound on the universal clock

Fix a pivot \(k\). On the projective torus define
\[
 d_k(z,w)=\sqrt{D_{a,k}(zw^{-1})}.                         \tag{20}
\]
After division by the pivot phase, this is the weighted \(L^2\) chord
pseudometric, so it is translation invariant and obeys the triangle
inequality.

Let
\[
 W=B_{a,k}(\eta/16).                                      \tag{21}
\]
Any alternating product of four points of \(W\) lies in
\(B_{a,k}(\eta)\), because four \(d_k\)-radii
\(\sqrt{\eta/16}\) add to \(\sqrt\eta\). By `(10)`,
\[
 (W-W)-(W-W)\subseteq A_a(\eta).                          \tag{22}
\]

Choose a maximal family \(F\) of pairwise disjoint translates of \(W\).
Positive Haar volume makes \(F\) finite, and
\[
 |F|\,m_J(W)\leq1.                                       \tag{23}
\]
Maximality gives the standard Ruzsa covering
\[
 \mathbb T^J=F+(W-W).                                     \tag{24}
\]
Among
\[
 0,\omega,\omega^2,\ldots,\omega^{|F|}
\]
two points lie in the same member of this cover. Their quotient has the
form `(22)`, so it belongs to \(A_a(\eta)\). Thus every packet returns by
tick \(|F|\).

The weighted average in `(5)` implies that some pivot has
\[
 m_J(B_{a,k}(\eta/16))>\tfrac12V_a(\eta/16).               \tag{25}
\]
Using this pivot in `(23)`--`(24)` gives
\[
 T_a(\eta)<\frac{2}{V_a(\eta/16)},                         \tag{26}
\]
which is the rightmost inequality in `(URL)`.

### 5.1 Return after every prescribed delay

The base clock in `(8)` is a positive near-hit, not by itself an
exit-conditioned first return. It nevertheless yields a genuine delayed law
without any new premise. For \(M\in\mathbb N\), apply `(8)` to the packet
\[
 \omega^{M+1}=(\omega_j^{M+1})_{j\in J}.                   \tag{27}
\]
There is \(1\leq q\leq T_a(\eta)\) for which this packet returns. Therefore
\[
 M<n=q(M+1)\leq(M+1)T_a(\eta)                             \tag{28}
\]
and the original packet returns at tick \(n\). If the system has exited the
target by tick \(M\), this is a post-exit recurrence.

Consequently
\[
 \Gamma_a(\eta)\leq T_a(\eta),                            \tag{26a}
\]
which proves the remaining central inequality in `(URL)`. The first
post-exit recurrence can only occur earlier than the supplied tick. No
formula for the first exit time itself is inferred.

## 6. Positivity in countably infinite dimension

Fix \(k\) and \(\delta>0\). Choose a finite set \(F\ni k\) such that
\[
 \sum_{j\notin F}a_j<\delta/4.                             \tag{29}
\]
The tail contributes at most \(2\sum_{j\notin F}a_j<\delta/2\) to
\(D_{a,k}\). Restrict the finitely many relative head phases to a sufficiently
small open arc so their total contribution is below \(\delta/2\). The
resulting positive-volume cylinder lies inside \(B_{a,k}(\delta)\).
Therefore every term in `(5)` is positive and
\[
 0<V_a(\delta)\leq1,\qquad 0\leq C_a(\delta)<\infty.       \tag{30}
\]

This is what makes `(URL)` genuinely infinite rather than a sequence of
unquantified finite truncations.

## 7. Exact quantum realization

Let \(U\) be a unitary operator and \(\psi\) a unit vector whose spectral
measure is pure point. Enumerate its atoms. Their masses \(a_j\) form a
finite or countably infinite probability vector and their unit-circle
eigenphases form \(\omega\). Then
\[
 |\langle\psi,U^n\psi\rangle|
 =\left|\sum_ja_j\omega_j^n\right|.                       \tag{31}
\]

Conversely, every pair \((a,\omega)\) is realized on
\(\ell^2(J)\) by
\[
 Ue_j=\omega_je_j,\qquad
 \psi=\sum_j\sqrt{a_j}\,e_j.                              \tag{32}
\]
Hence `(URL)` is exactly a theorem about all pure-point quantum survival
records, not an analogy with them.

The same scalar law applies to any normalized stationary quantum
autocorrelation already represented by a positive spectral measure. An
extension to a claimed state-distance law requires a separate exact
positive-measure representation and may not be inferred from `(URL)`.

## 8. Maximal all-spectrum boundary

For an arbitrary unitary spectral probability law \(\mu\), let
\[
 p=\mu_{\mathrm{pp}}(\mathbb T)
\]
be its total atomic mass. The existing stationary distribution theorem has
the following paper-level consequence:

\[
 \mu\text{ is pure point}
 \quad\Longleftrightarrow\quad
 \text{every subunit survival-fidelity target is syndetic}.           \tag{33}
\]

If \(\mu\) is pure point, uniform almost periodicity proves bounded-gap
return. If \(p<1\), every return target strictly above \(p^2\) has zero
asymptotic density; a syndetic stricter target would force positive lower
density, contradiction. Thus no finite universal high-fidelity horizon
exists beyond the pure-point sector.

Equation `(33)` prevents the countable theorem from being promoted
incorrectly to continuous spectra. It also makes the domain maximal for
bounded-gap high-fidelity recurrence: pure point is not a convenient
assumption but the exact boundary.

Sparse exceptional recurrence of continuous spectra remains possible and is
not classified by `(URL)`. A final title may use “quantum recurrence” only
if the manuscript defines recurrence operationally as bounded-gap or
spectrum-uniform high-fidelity return and proves `(31)` prominently.

## 9. Why this is one law rather than a collage

The same scalar \(C_a\) appears at both ends of one theorem chain:

```text
intrinsic circular phase-space information
  -> exact rarity of the quantum fidelity target
  -> least deadline valid for every compatible spectrum.
```

The finite water law, high-resolution exponent, effective dimension,
countable recurrence, and target-volume bounds become consequences or
approximations of this object. Observer graphs may be retained only as a
derived method for computing the dimension of \(C_a\) in finite models; they
must not become a second centre of the paper.

## 10. Immediate falsifiers

The candidate is false if any of the following occurs:

1. `(12)` fails for a countable probability vector;
2. the pivot Markov step does not yield `(15)` after boundary handling;
3. a circular ball has zero product-Haar volume at positive radius;
4. multiplication by \(n\) fails to preserve Haar probability on
   \(\mathbb T^J\);
5. the fourfold difference inclusion `(22)` fails for the chord
   pseudometric;
6. a maximal disjoint translate family need not be finite or need not give
   `(24)`;
7. a pure-point quantum survival amplitude cannot be represented by `(29)`;
8. `(33)` admits a non-pure-point counterexample with every high-fidelity
   target syndetic.

## 11. Entropy is not the recurrence clock

The scientific question is not merely whether recurrence occurs. Quantum
gravity, statistical mechanics, and many-body physics routinely estimate
very-late return scales from entropy or effective dimension. Those quantities
cannot be complete recurrence clocks.

The corpus already contains two unconditional separation mechanisms:

1. two full-rank qutrit clocks with the same Hamiltonian, the same density
   operator spectrum, the same Hilbert--Schmidt speed, and the same
   symmetric-logarithmic-derivative quantum Fisher information, but
   different global recurrence laws;
2. normalized cyclic quantum histories with identical complete local
   transition-amplitude jets but different persistent recurrence.

Equality of the density-operator spectrum forces equality of every
unitarily invariant spectral entropy, including von Neumann entropy.
Therefore no function of thermodynamic/state entropy, local speed, or local
time information alone can determine recurrence.

`(URL)` supplies the positive replacement:
\[
\text{recurrence clock}
\quad\longleftarrow\quad
\text{information volume of the actual return target},                 \tag{34}
\]
not the total number of states or the entropy of the initial density
operator.

The admissible popular statement is:

> Systems containing the same amount of quantum information can remember
> their past on radically different timescales; the clock is set by the
> rarity of phase configurations that reconstruct the state.

The stronger slogan “black-hole entropy is wrong” is not admissible.
For a holographic model with a discrete boundary spectrum, `(URL)` constrains
its quantum survival or autocorrelation recurrence. It does not derive a
bulk black-hole spectrum, identify Bekenstein--Hawking entropy with any
quantity in `(URL)`, or prove a statement in dynamical gravity.

## 12. Primary-literature boundary

The following parents have been identified:

1. Kac's 1943 value-distribution theorem for trigonometric sums supplies a
   classical parent for Haar phase distributions.
2. Ruzsa covering and compact-group translate-covering theory supply the
   maximal-disjoint-translate mechanism in Section 5.
3. Bohr almost periodicity supplies qualitative bounded-gap recurrence for
   pure-point spectra.
4. Kotowski--Oszmaniec (2026) prove finite-dimensional deterministic
   recurrence bounds, random-Hamiltonian lower bounds, and hard
   effective-support refinements. Their theorem is finite-dimensional and
   dimension/support based.
5. Gupta--Short (2026) prove finite-system recurrence bounds through
   simultaneous Diophantine approximation.
6. Campos Venuti (2015) gives generic recurrence estimates in terms of
   energy scale and effective dimension.
7. Gimeno--Sotoca (2017) already cover qualitative finite and countably
   discrete mixed-state recurrence.
8. Barbon--Rabinovici and later black-hole literature use very-late
   correlator recurrence to diagnose discreteness and unitarity in
   holographic systems; this is motivation, not a theorem parent.

The exact-object search through 29 July 2026 has not located a primary source
joining arbitrary finite/countable weights, exact weighted-phasor target
volume, a support-free circular information, spectrum-uniform minimax
deadline, and the pure-point maximality boundary. Absence from search is not
proof of priority; classification remains open.

## 13. Rediscovery kill tests

The novelty is killed if prior literature already contains, for arbitrary
finite and countable probability vectors, an equivalent theorem joining:

1. exact weighted phasor target volume;
2. one intrinsic non-Gaussian circular information;
3. a spectrum-uniform deterministic recurrence deadline;
4. an exit-conditioned factor valid after every witnessed exit;
5. matching lower and upper information bounds without an explicit
   support-size remainder;
6. the pure-point maximality boundary.

Kac recurrence, value distributions of trigonometric sums, Ruzsa covering,
Bohr almost periodicity, or small-ball estimates separately are parents, not
the joined object. A published theorem combining them into `(URL)` up to
universal radius constants kills this candidate.

## 14. Nature significance kill tests

Reject this as the master paper if hostile review finds any of:

1. `(URL)` is merely a renamed general compact-group covering theorem with
   no new quantum or weighted-circular content;
2. radius rescaling hides the same support-linear weakness as the old
   \(O(r)\) remainder in every scientifically relevant regime;
3. minimax over compatible spectra answers no question physicists ask;
4. the exact infinite extension has no consequence beyond qualitative
   almost periodicity;
5. no observable protocol estimates \(I_a\), \(C_a\), or tests the deadline
   inequality;
6. arbitrary continuous spectra, open systems, or gravity are implied in
   title or abstract without an exact theorem;
7. the result cannot be stated as one worldview-changing sentence without
   importing unsupported cosmology.

## 15. Required next gates

- [x] one exact candidate with every/any finite-and-countable quantifiers
- [x] dependency-closed paper proof V1
- [x] return after every prescribed delay
- [x] explicit continuous-spectrum maximality boundary
- [ ] specialist attack on all boundary conventions and integer constants
- [ ] exact-object primary-literature audit
- [ ] decide `[NEW KNOWLEDGE]`, `[BRIDGE]`, or `[REDISCOVERED]`
- [ ] prove an operational estimator or experimental inequality
- [ ] authorize Lean only after the preceding gates pass
- [ ] formalize `(URL)`, quantum realization, and maximality without axioms
- [ ] Nature hostile review and manuscript integration
