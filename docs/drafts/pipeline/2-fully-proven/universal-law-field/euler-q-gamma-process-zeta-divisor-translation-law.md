# Euler q-Gamma process, random-integer law, and zeta-divisor translation law

- **ID:** ULF-EQG-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Constitutive Process Mathematics local-to-global product gate
- **Statement:** A normalized tensor product of prime-indexed q-Gamma processes is an explicit
  random-integer law whose exponential response has a meromorphic zeta ladder; its unit tilt has
  translation boundary exactly the pulled-back Riemann-zeta divisor.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [CPM LOCAL-TO-GLOBAL]
  [UNCONDITIONAL ARITHMETIC SOURCE RELATION] [POSITIVE NORMALIZATION]
  [DIVISOR LANDING] [GENUS-ONE ERASURE CLASSIFIED] [LEAN FINITE CORE PLANNED] [NOT RH]

## 1. Why this is a field theorem

This construction does not begin with a zeta zero or an RH route. It begins with one local positive
constitutive process at every prime, composes them by the ordinary tensor product of probability
laws, and asks what global intervention law composition forces. The answer is a source-normalized
translation equation whose Cartier divisor is the complete zeta divisor.

The theorem therefore supplies the first arithmetic local-to-global operation for Constitutive
Process Mathematics:

\[
\text{local positive processes}
\longrightarrow
\text{global process}
\longrightarrow
\text{translation response}
\longrightarrow
\text{arithmetic divisor}.
\]

The ingredients are classical. The load-bearing content is their typed composition as one process
and the exact comparison with the canonical cumulant renormalization.

## 2. Local q-Gamma law

For \(0<q<1\), write

\[
(a;q)_n=\prod_{j=0}^{n-1}(1-aq^j),
\qquad
(a;q)_\infty=\prod_{j=0}^{\infty}(1-aq^j).
\]

Define

\[
w_{q,n}=(q;q)_\infty\frac{q^n}{(q;q)_n},
\qquad
x_{q,n}=n\log q-\log(1-q).
\tag{EQG.1}
\]

The q-binomial theorem gives

\[
\sum_{n\ge0}w_{q,n}=1,
\qquad
\sum_{n\ge0}w_{q,n}e^{s x_{q,n}}
=\Gamma_q(1+s)
\tag{EQG.2}
\]

for \(\Re s>-1\), where

\[
\Gamma_q(z)=(1-q)^{1-z}\frac{(q;q)_\infty}{(q^z;q)_\infty}.
\]

Its exact unit-intervention law is

\[
\Gamma_q(2+s)=\frac{1-q^{1+s}}{1-q}\Gamma_q(1+s),
\qquad
\Gamma_q(1)=\Gamma_q(2)=1.
\tag{EQG.3}
\]

## 3. Global prime product and random integer

Fix a real parameter \(\sigma>1\), put \(q_p=p^{-\sigma}\), and let the variables
\((N_p)_p\) be independent with

\[
\mathbb P(N_p=n)=w_{q_p,n}.
\tag{EQG.4}
\]

### Theorem 3.1 — finite support and arithmetic law

Almost surely only finitely many \(N_p\) are nonzero. Consequently

\[
M=\prod_p p^{N_p}
\tag{EQG.5}
\]

is an ordinary positive integer almost surely. Its mass function is

\[
\boxed{
\mathbb P_\sigma(M=m)
=C_\sigma\,
\frac{m^{-\sigma}}
{\displaystyle\prod_p(p^{-\sigma};p^{-\sigma})_{v_p(m)}} ,
}
\tag{EQG.6}
\]

where all but finitely many denominator factors equal one and

\[
\boxed{
C_\sigma
=\prod_p(p^{-\sigma};p^{-\sigma})_\infty
=\prod_{k=1}^{\infty}\zeta(\sigma k)^{-1}>0.
}
\tag{EQG.7}
\]

#### Proof

Since \(w_{q,0}=(q;q)_\infty\),

\[
\mathbb P(N_p>0)
=1-\prod_{k\ge1}(1-p^{-\sigma k})
\le \sum_{k\ge1}p^{-\sigma k}
=\frac{p^{-\sigma}}{1-p^{-\sigma}}.
\]

The sum over primes converges for \(\sigma>1\). Borel--Cantelli proves finite support.
Independence and unique factorization then give

\[
\prod_p
\left((q_p;q_p)_\infty
\frac{q_p^{v_p(m)}}{(q_p;q_p)_{v_p(m)}}\right),
\]

which is (EQG.6). Absolute convergence permits interchanging the prime and occupation products:

\[
\prod_p\prod_{k\ge1}(1-p^{-\sigma k})
=\prod_{k\ge1}\prod_p(1-p^{-\sigma k})
=\prod_{k\ge1}\zeta(\sigma k)^{-1}.
\]

The logarithms converge absolutely because
\(\sum_{p,k}p^{-\sigma k}<\infty\). This also proves positivity. QED.

## 4. Global constitutive response

Define the global logarithmic observable

\[
X_\sigma=\sum_p x_{q_p,N_p}.
\]

Finite support and Euler's product give the exact arithmetic coordinate

\[
\boxed{X_\sigma=\log\zeta(\sigma)-\sigma\log M.}
\tag{EQG.8}
\]

Let

\[
F_\sigma(s)=\mathbb E_\sigma e^{sX_\sigma}.
\tag{EQG.9}
\]

### Theorem 4.1 — Euler q-Gamma response

On

\[
\Re s>\frac1\sigma-1,
\tag{EQG.10}
\]

the following products and series converge normally on compact subsets:

\[
\boxed{
F_\sigma(s)
=\prod_p\Gamma_{p^{-\sigma}}(1+s)
=\zeta(\sigma)^s C_\sigma
  \prod_{k=0}^{\infty}\zeta\!\left(\sigma(1+s+k)\right).
}
\tag{EQG.11}
\]

Equivalently,

\[
F_\sigma(s)
=\zeta(\sigma)^s C_\sigma
\sum_{m\ge1}
\frac{m^{-\sigma(1+s)}}
{\displaystyle\prod_p(p^{-\sigma};p^{-\sigma})_{v_p(m)}}.
\tag{EQG.12}
\]

#### Proof

Independence and (EQG.2) give the prime product. Expanding q-Gamma gives

\[
\Gamma_{p^{-\sigma}}(1+s)
=(1-p^{-\sigma})^{-s}
\frac{(p^{-\sigma};p^{-\sigma})_\infty}
{(p^{-\sigma(1+s)};p^{-\sigma})_\infty}.
\]

Multiplying the first factors gives \(\zeta(\sigma)^s\); multiplying the numerators
gives \(C_\sigma\); and the denominator gives

\[
\prod_{k\ge0}\prod_p
(1-p^{-\sigma(1+s+k)})^{-1}
=\prod_{k\ge0}\zeta(\sigma(1+s+k)).
\]

On a compact subset of (EQG.10), the local logarithm is uniformly
\(O(p^{-\sigma}+p^{-\sigma(1+\Re s)})\), whose prime sum converges. This proves normal
convergence and justifies every interchange. Formula (EQG.12) follows either from (EQG.6) and
(EQG.8) or by expanding the Euler product. QED.

## 5. Meromorphic continuation and source-normal translation

### Theorem 5.1 — global continuation and exact tilt

Formula (EQG.11) defines a meromorphic continuation of \(F_\sigma\) to all of \(\mathbb C\).
It satisfies the meromorphic identity

\[
\boxed{
F_\sigma(s+1)
=\frac{\zeta(\sigma)}{\zeta(\sigma(1+s))}F_\sigma(s).
}
\tag{EQG.13}
\]

In particular,

\[
F_\sigma(0)=F_\sigma(1)=1.
\tag{EQG.14}
\]

Therefore

\[
\frac{d\mathbb P_\sigma^*}{d\mathbb P_\sigma}
=e^{X_\sigma}
=\zeta(\sigma)M^{-\sigma}
\tag{EQG.15}
\]

is already normalized: it is a genuine exponential intervention, not a fitted scalar correction.

#### Proof

For a compact set of \(s\)-values, all sufficiently large \(k\) place
\(\sigma(1+s+k)\) in a fixed far-right half-plane. There
\(\zeta(w)-1=O(2^{-\Re w})\) uniformly, so the tail of (EQG.11) converges normally to a
holomorphic nonzero function. Only finitely many zeta factors remain, proving meromorphic
continuation.

Shifting \(s\) by one cancels the entire zeta ladder except its first factor:

\[
\frac{F_\sigma(s+1)}{F_\sigma(s)}
=\zeta(\sigma)
\frac{\prod_{k\ge0}\zeta(\sigma(2+s+k))}
{\prod_{k\ge0}\zeta(\sigma(1+s+k))}
=\frac{\zeta(\sigma)}{\zeta(\sigma(1+s))}.
\]

At \(s=0\), this ratio is one. The probability interpretation gives (EQG.15). QED.

## 6. Exact Cartier-divisor landing

Let \(T(s)=s+1\), \(\phi_\sigma(s)=\sigma(1+s)\), and let \(\operatorname{div}(f)\)
denote the Cartier divisor of a nonzero meromorphic function.

### Theorem 6.1 — translation divisor transgression

\[
\boxed{
T^*\operatorname{div}(F_\sigma)
-\operatorname{div}(F_\sigma)
=-\phi_\sigma^*\operatorname{div}(\zeta).
}
\tag{EQG.16}
\]

Equivalently, at every \(a\in\mathbb C\),

\[
\operatorname{ord}_{a+1}F_\sigma-
\operatorname{ord}_{a}F_\sigma
=-\operatorname{ord}_{\sigma(1+a)}\zeta.
\tag{EQG.17}
\]

If \(\rho\) is a nontrivial zeta zero of multiplicity \(m_\rho\), then

\[
a_\rho=\frac{\rho}{\sigma}-1
\]

satisfies the sharper clean-landing law

\[
\boxed{
\operatorname{ord}_{a_\rho}F_\sigma=m_\rho,
\qquad
F_\sigma(a_\rho+1)\ne0,\infty.
}
\tag{EQG.18}
\]

#### Proof

Taking divisors in (EQG.13) proves (EQG.16); nonzero affine pullback preserves local order and
gives (EQG.17). At \(a_\rho\), the \(k=0\) factor in (EQG.11) is \(\zeta(\rho)\). Every
factor with \(k\ge1\) has argument \(\rho+\sigma k\), whose real part exceeds one, and is
therefore finite and nonzero. After translating by one, every factor has argument
\(\rho+\sigma(1+k)\), again in the zero-free half-plane. QED.

This is the promised unconditional arithmetic source relation. It does not prove RH: it lands the
divisor faithfully but does not constrain its horizontal location.

## 7. Hypertranscendence and global process memory

### Theorem 7.1

The meromorphic response \(F_\sigma\) is hypertranscendental over \(\mathbb C(s)\).

#### Proof

Riemann zeta is hypertranscendental. Indeed, if zeta were differentially algebraic, then so would
be \(\zeta(1-s)\). Riemann's functional equation would make \(\Gamma(1-s)\) a quotient of
differentially algebraic meromorphic functions and elementary differential-algebraic factors,
contradicting Hoelder's theorem for Gamma.

If \(F_\sigma\) were differentially algebraic, so would its translate \(F_\sigma(s+1)\) and
their quotient. Equation (EQG.13) would make \(\zeta(\sigma(1+s))\) differentially algebraic.
Affine change of variable would make zeta differentially algebraic, contradiction. QED.

Thus the local-to-global operation preserves the maximal differential-memory phase and makes its
arithmetic carrier explicit.

## 8. Positive recurrent observer and open history

On

\[
\mathcal H_\sigma=L^2(\mathbb N_{>0},\mathbb P_\sigma),
\]

let \(X_\sigma\) act by multiplication and put \(U_t=e^{itX_\sigma}\), \(\Omega=1\).

### Theorem 8.1

The operator \(X_\sigma\) has compact resolvent, the orbit \(U_t\Omega\) is norm-precompact and
recurrent, and there are arbitrarily large \(t_j\) with

\[
U_{t_j}\Omega\to\Omega,
\qquad
\|t_jX_\sigma\Omega\|\to\infty.
\tag{EQG.19}
\]

#### Proof

The spectral values are \(\log\zeta(\sigma)-\sigma\log m\), one for each positive integer
\(m\), and their absolute values tend to infinity. Hence the diagonal resolvent is compact.
Analyticity of (EQG.9) around zero gives \(X_\sigma\Omega\in\mathcal H_\sigma\) and nonzero
variance. Finite-head simultaneous phase approximation, followed by a uniform probability-tail
estimate, gives arbitrarily large return times in the \(\Omega\)-norm. The lifted history has norm
\(|t|\|X_\sigma\Omega\|\), proving escape along the same sequence. QED.

## 9. Canonical genus-one renormalization and divisor erasure

The full probability process exists on ordinary integers only for \(\sigma>1\). The local response
admits a canonical first-activation subtraction beyond that chamber.

For \(\sigma>\tfrac12\), put \(q_p=p^{-\sigma}\) and

\[
\ell_{p,\sigma}(s)=q_p(s-1)+q_p^{1+s}.
\tag{EQG.20}
\]

Define

\[
\mathcal R_\sigma(s)
=\prod_p\Gamma_{q_p}(1+s)e^{-\ell_{p,\sigma}(s)}.
\tag{EQG.21}
\]

### Theorem 9.1 — half-plane extension and zero-free boundary

The product (EQG.21) converges normally and is holomorphic and zero-free on

\[
\Re s>\frac1{2\sigma}-1.
\tag{EQG.22}
\]

Let \(z=\sigma(1+s)\), define the prime zeta function
\(P(w)=\sum_pp^{-w}\) for \(\Re w>1\), and define the genus-one Euler unit

\[
\mathcal E_1(z)=\prod_p(1-p^{-z})e^{p^{-z}},
\qquad \Re z>\frac12.
\tag{EQG.23}
\]

Then

\[
\boxed{
\frac{\mathcal R_\sigma(s+1)}{\mathcal R_\sigma(s)}
=\frac{\mathcal E_1(z)}{\mathcal E_1(\sigma)}
  e^{-P(\sigma+z)}.
}
\tag{EQG.24}
\]

The right side is holomorphic and zero-free throughout \(\Re z>\tfrac12\). Thus the canonical
square-summable renormalization erases the entire translation divisor.

#### Proof

The exact logarithm of the local response is

\[
\log\Gamma_q(1+s)
=-s\log(1-q)
 +\sum_{n\ge1}\frac{q^{n(1+s)}-q^n}{n(1-q^n)}.
\tag{EQG.25}
\]

Uniformly on compact subsets of (EQG.22), subtracting (EQG.20) leaves

\[
O(q^2)+O(q^{2(1+\Re s)})+O(q^{2+\Re s}).
\]

All three prime sums converge exactly under \(\sigma>\tfrac12\) and (EQG.22). Normal
convergence of logarithms proves that \(\mathcal R_\sigma\) is holomorphic and nonzero.

Writing \(x=q_p^{1+s}=p^{-z}\), one computes

\[
\ell_{p,\sigma}(s+1)-\ell_{p,\sigma}(s)
=q_p-(1-q_p)x.
\]

Combining this with (EQG.3) gives

\[
\frac{\Gamma_{q_p}(2+s)e^{-\ell_{p,\sigma}(s+1)}}
{\Gamma_{q_p}(1+s)e^{-\ell_{p,\sigma}(s)}}
=\frac{(1-x)e^x}{(1-q_p)e^{q_p}}e^{-q_px}.
\]

Multiplication over primes is absolutely convergent and gives (EQG.24). Every local factor is
nonzero when \(\Re z>\tfrac12\), and its logarithm is square-summable over primes. QED.

### Corollary 9.2 — exact location of the lost arithmetic information

For \(\Re z>1\),

\[
\mathcal E_1(z)=\zeta(z)^{-1}e^{P(z)}.
\tag{EQG.26}
\]

Equivalently, with

\[
H(z)=\sum_{m\ge2}\frac{P(mz)}m,
\]

which is holomorphic for \(\Re z>\tfrac12\),

\[
\mathcal E_1(z)=e^{-H(z)},
\qquad
e^{-P(z)}=\zeta(z)^{-1}e^{H(z)}.
\tag{EQG.27}
\]

Therefore:

- every occupation grade at least two forms a holomorphic zero-free unit past the critical
  half-plane;
- the exponentiated first prime cumulant carries exactly \(-\operatorname{div}(\zeta)\);
- deleting that cumulant is precisely what turns the source response into the zero-free
  renormalized process.

This is a sharp non-erasure boundary, not merely the slogan that positivity loses phase.

## 10. Conjecture, proof, and failure loops

1. **Prime-indexed q-Gamma values must be algebraically independent before anything useful
   follows.** False. Cross-prime value independence is irrelevant here; ordinary product
   normalization and the local translation equation already force (EQG.13).

2. **The global prime product cannot be normalized.** False for \(\sigma>1\). The product is the
   explicit probability (EQG.6). True at and below the finite-activity wall if one insists on an
   ordinary integer with finitely many active primes.

3. **Positive recurrence should constrain zeta zeros directly.** False. Positivity lives in the
   original moment half-plane; the divisor appears only after meromorphic continuation beyond its
   first pole.

4. **Canonical genus-one renormalization retains the divisor.** False by (EQG.24). Its translation
   response is a holomorphic unit. The exact survivor is the first-cumulant Cartier carrier
   (EQG.27).

5. **The divisor relation proves RH.** False. Equation (EQG.18) embeds every nontrivial zero with
   multiplicity but provides no horizontal localization principle.

## 11. Corpus and literature collision audit

The prior card `gamma-q-multi-q-dss.md` studied algebraic independence of the separate values
\((1/p;1/p)_\infty\). It neither constructs the normalized product probability nor derives the
translation-divisor law. Its cross-prime conjecture is therefore bypassed rather than solved.

The genus-one erasure mechanism itself is occupied. The corpus card
`prime-diagonal-singular-trace-dephasing.md` already identifies the Hilbert--Carleman determinant
as the zero-free higher-prime-power tail and the missing prime trace as the divisor carrier.
Froberg's classical prime-zeta continuation is the analytic parent. The present theorem does not
claim those ingredients as new. Its contribution is the exact positive q-Gamma process whose
source-normal exponential intervention produces that decomposition and lands the complete divisor.

Primary parents:

- P. I. Pastro, *A q-analogue of a theorem of Hoelder*, Rendiconti del Seminario Matematico della
  Universita di Padova 70 (1983), 47--53.
- C.-E. Froberg, *On the prime zeta function*, BIT 8 (1968), 187--202.
- The q-binomial theorem and Jackson q-Gamma identities, as catalogued in DLMF Chapter 17.

Broad exact-phrase and formula searches found no source stating the assembled random-integer law,
q-Gamma Euler response, normalized tilt, and divisor transgression as one theorem. Priority is not
needed for the CPM field claim; the formulas and their coupling are what matter.

## 12. Scope

- The probability theorem requires \(\sigma>1\).
- The zero-free renormalized process requires \(\sigma>\tfrac12\).
- The construction is unconditional and pre-zero; zeros enter only through the forced meromorphic
  response.
- No physical clock, cost, Stokes contact, or wormhole interpretation is asserted.
- The theorem gives an arithmetic source relation and an exact erasure classification, not RH.
- The finite algebraic normalization/translation core is the first Lean target. Infinite-product
  meromorphy and Cartier divisors remain paper-level until matching APIs exist.

## Gates

- [x] local positive q-Gamma process
- [x] global product probability and random-integer law
- [x] normal convergence in the moment chamber
- [x] global meromorphic continuation
- [x] normalized exponential intervention
- [x] exact zeta-divisor translation law and multiplicity landing
- [x] global hypertranscendence
- [x] recurrent observer and open lifted history
- [x] canonical genus-one renormalization and divisor-erasure theorem
- [x] prior-corpus and literature collision audit
- [ ] finite unconditional core formalized in Lean
- [ ] critical-boundary process topology beyond genus one

## Log

- 2026-08-09 — dependency-closed paper theorem created after the CPM field pivot from route
  comparison to local-to-global constitutive-process composition.
