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
  [DIVISOR LANDING] [GENUS-ONE ERASURE CLASSIFIED] [LEAN LOCAL CORE]
  [GLOBAL THEOREM NOT LEAN-CERTIFIED] [NOT RH]
- **Lean local core:** `formal/GaloisForLFunctions/HTGeometry/QPochhammer.lean`
- **Lean finite exchange core:**
  `formal/GaloisForLFunctions/HTGeometry/EulerQGammaFiniteProcess.lean`

> **Proof gate:** Under the current project rule, only the local q-Pochhammer/q-Gamma process and
> finite exchange declarations listed above count as proved.  Global prime product, random-integer
> law, zeta product, meromorphic continuation, divisor landing, hypertranscendence, and recurrent
> GNS realization remain paper claims until separately certified in Lean.

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
- Lean now owns q-Pochhammer convergence/nonvanishing/shift, normalized q-Gamma translation,
  positive local weights, total mass one, the complete nonnegative-integral moment ladder, and the
  finite algebraic exchange/telescope. Infinite prime products, meromorphy, and Cartier divisors
  remain paper-only.

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
- [x] local q-Pochhammer/q-Gamma analytic infrastructure formalized in Lean
- [x] local positive mass-one law and complete integral response ladder formalized in Lean
- [x] finite unconditional exchange/telescope core formalized in Lean
- [ ] global prime probability and random-integer law formalized in Lean
- [ ] zeta product, meromorphic continuation, and divisor landing formalized in Lean
- [ ] hypertranscendence and recurrent/open-history realization formalized in Lean
- [ ] critical-boundary process topology beyond genus one

## Log

- 2026-08-09 — dependency-closed paper theorem created after the CPM field pivot from route
  comparison to local-to-global constitutive-process composition.
- 2026-08-09 — missing q-Pochhammer/q-Gamma infrastructure created in Lean; local mass-one law,
  normalized translation, and all nonnegative-integral moments certified. Global claims explicitly
  remain uncertified.

## Lean certification plan (opened 2026-08-10)

Sibling cards ULF-QGPRH-1 and ULF-QG5R-1 are now stage 3, so the corpus owns the whole *local*
layer this card needs: `qGammaWeight`/`qGammaWeight_hasSum_one`, `realQFactorial`,
`realQFactorialInf` with `realQFactorialInf_pos`/`_ne_zero`/`_le`, `qGeometricCoefficient` with
**`qGeometricCoefficient_hasSum : HasSum (qGeometricCoefficient q) (realQFactorialInf q)⁻¹`**
(this is the local Euler factor), the analytic `qGammaOn` layer, Jackson's translation law, the
q-digamma/Bell layer, **Pastro's q-Hölder theorem** (`qGamma_jet_annihilator_eq_zero`), the GNS
machinery (`QGammaSpace`, `qUnitary`, `dense_span_qOrbit`, `exists_unique_marked_intertwiner`,
diagonal unitaries and compact diagonal resolvents on `ℓ²`), and the classical
`hypertranscendental_gamma`.

Audited mathlib inputs: `EulerProduct.eulerProduct_hasProd` (for a multiplicative `f : ℕ → R` with
`f 0 = 0`, `f 1 = 1` and `Summable (‖f ·‖)`: `HasProd (fun p : Nat.Primes => ∑' e, f (p^e))
(∑' n, f n)`) — this is exactly (EQG.6)/(EQG.7); `riemannZeta` and its Euler product;
`Nat.factorization`, `Nat.primeFactors`, `Nat.factorization_mul`.

Planned modules.

1. `EulerQGammaGlobalLaw.lean` — **Theorem 3.1**.  `EulerSigma` (`1 < σ`), the local nome
   `eqgNome σ p = p^{-σ}` as a `RealEulerNome`, the arithmetic weight
   `eqgWeight σ m = m^{-σ} / ∏_{p ∣ m} (q_p;q_p)_{v_p(m)}` (zero at `m = 0`), its multiplicativity
   on coprimes, and its summability through the uniform denominator bound
   `(q;q)_n ≥ exp(−4q)` (from `1 − y ≥ exp(−2y)` on `[0,1/2]`, valid because `q_p ≤ 2^{-σ} < 1/2`)
   together with `∑_{p ∣ m} p^{-σ} ≤ ∑_{n ≥ 2} n^{-σ}`.  Then `eulerProduct_hasProd` plus
   `qGeometricCoefficient_hasSum` gives
   `HasProd (fun p => (q_p;q_p)_∞⁻¹) (∑' m, eqgWeight σ m)`, hence **(EQG.7)** `C_σ` as the
   convergent prime product `∏_p (q_p;q_p)_∞ > 0` and **(EQG.6)** the mass function with
   `∑' m, C_σ · eqgWeight σ m = 1`.  The almost-sure finite support of `(N_p)` is the same
   statement read on the product law, and is certified in the form actually used: the law lives on
   ordinary positive integers.
2. `EulerQGammaResponse.lean` — **Theorem 4.1**, (EQG.8)–(EQG.12): the global observable
   `X_σ = log ζ(σ) − σ log M`, the response `F_σ(s) = ∑_m P_σ(m) e^{sX_σ(m)}`, its Dirichlet form
   (EQG.12), and the prime-product form (EQG.11) with the zeta ladder, by the same Euler-product
   route applied at `σ(1+s)` together with the `ζ(σk)^{-1}` telescope for `C_σ`.
3. `EulerQGammaContinuation.lean` — **Theorem 5.1**: normal convergence of the ladder tail on
   compact sets, the meromorphic continuation, the translation law **(EQG.13)** and (EQG.14),
   (EQG.15).
4. `EulerQGammaDivisor.lean` — **Theorem 6.1**, (EQG.16)–(EQG.18): the order/divisor transgression,
   reusing the corpus's finite ladder core `EulerQGammaFiniteProcess` and the meromorphic
   order layer.
5. `EulerQGammaHypertranscendence.lean` — **Theorem 7.1**: hypertranscendence of `F_σ`, from
   hypertranscendence of `ζ` (functional equation plus the corpus's `hypertranscendental_gamma`)
   and (EQG.13).
6. `EulerQGammaObserver.lean` — **Theorem 8.1**: the `L²(ℕ_{>0}, P_σ)` realization, the diagonal
   generator `X_σ` with compact resolvent, and recurrence of the orbit — the same shape as the
   already-certified `ConstitutiveQGammaProcess` GNS layer, over the arithmetic index set.
7. `EulerQGammaGenusOne.lean` — **Theorem 9.1**, (EQG.20)–(EQG.24): the genus-one subtraction, its
   half-plane holomorphy and zero-freeness, and the divisor-erasure identity.

### Step 1 is done — Theorem 3.1 is certified

`GaloisForLFunctions/HTGeometry/EulerQGammaGlobalLaw.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,543-job build green).

- `EulerSigma` (the chamber `σ > 1`), the local nome `eqgQ σ n = n^{-σ}` with
  `eqgQ_pos`, `eqgQ_lt_one`, **`eqgQ_le_half`** (every prime nome is at most `1/2`, because
  `p^{-σ} ≤ p^{-1} ≤ 1/2`), and `eqgNome σ p : RealEulerNome`.
- **`exp_neg_two_mul_le_one_sub`** (`exp(−2x) ≤ 1 − x` on `[0,1/2]`, through `1 + 2x ≤ exp(2x)`)
  and **`exp_le_eqgLocalFactorial`** — the uniform lower bound `(q;q)_n ≥ exp(−4q)` for a nome at
  most `1/2`.  This is what makes the arithmetic weight summable without any prime-counting input.
- The arithmetic weight `eqgWeight σ m = m^{-σ}/∏_{p ∣ m}(q_p;q_p)_{v_p(m)}` with `eqgWeight_zero`,
  `eqgWeight_one`, `eqgWeight_nonneg`, **`eqgDenom_mul`** and **`eqgWeight_mul`** (multiplicativity
  on coprimes, from `Nat.primeFactors_mul` and `Nat.factorization_mul`), and
  **`eqgWeight_prime_pow`** — *the local Euler factor is exactly the corpus's
  `qGeometricCoefficient`*, so the local q-binomial normalisation is the local Euler factor.
- `eqgTail`, `summable_eqgQ`, `sum_eqgQ_le_tail`, **`eqgDenom_lower`**
  (`∏_{p ∣ m}(q_p;q_p)_{v_p(m)} ≥ exp(−4∑_n n^{-σ})`, uniformly in `m`), `eqgWeight_le`, and
  **`summable_eqgWeight`**.
- **`eqgEulerProduct`** — mathlib's `EulerProduct.eulerProduct_hasProd` applied to the arithmetic
  weight gives `HasProd (fun p => (q_p;q_p)_∞⁻¹) (∑' m, eqgWeight σ m)`, i.e. the local
  normalisations multiply to the global one.
- **Equation (EQG.7)**: `eqgTotal`, `eqgTotal_pos`, `eqgConst σ = (∑' m, eqgWeight σ m)⁻¹` with
  `eqgConst_pos` and **`eqgConst_hasProd : HasProd (fun p => (q_p;q_p)_∞) (eqgConst σ)`** — the
  normalising constant *is* the convergent prime product, and it is positive.
- **Equation (EQG.6) and Theorem 3.1**: `eqgMass σ m = C_σ · eqgWeight σ m`, `eqgMass_pos` (every
  positive integer has positive mass) and **`eqgMass_hasSum_one`** — the mass function is a
  probability law on the positive integers.  This is the certified form of "almost surely only
  finitely many `N_p` are nonzero": the composed law lives on ordinary integers and has total
  mass one.

`#print axioms` on `eqgMass_hasSum_one`, `eqgConst_hasProd`, `eqgEulerProduct`, `eqgConst_pos` and
`eqgMass_pos` reports only `propext`, `Classical.choice`, `Quot.sound`.

Still open on this card: steps 2–7 of the plan above (Theorems 4.1, 5.1, 6.1, 7.1, 8.1, 9.1).

### Step 2a is done — the Dirichlet Euler product

`GaloisForLFunctions/HTGeometry/EulerQGammaDirichlet.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,545-job build green).

Shifting the numerator exponent of the arithmetic weight from `σ` to an arbitrary complex `w`,
with the nomes still taken from `σ`, keeps the weight multiplicative, and its **local Euler factor
becomes the complex q-binomial series** at `a = p^{-w}` with nome `q_p`.  The corpus's
`qBinomial_hasSum` evaluates that series as `(p^{-w}; q_p)_∞⁻¹`, so the whole global Dirichlet
series collapses to a prime product of reciprocal q-Pochhammer symbols.

- `eqgWeightRe σ x m` — the real-exponent weight, with `eqgWeightRe_nonneg`, `eqgWeightRe_le`
  (the same uniform denominator bound `exp(−4∑ n^{-σ})`, which does not depend on the exponent)
  and **`summable_eqgWeightRe`** for every `x > 1`.
- `eqgTerm σ w m = m^{-w}/∏_{p ∣ m}(q_p;q_p)_{v_p(m)}` with `eqgTerm_zero`, `eqgTerm_one`,
  **`norm_eqgTerm`** (`‖eqgTerm σ w m‖ = eqgWeightRe σ (Re w) m`), `summable_norm_eqgTerm` for
  `Re w > 1`, and **`eqgTerm_mul`** (multiplicativity on coprimes, through
  `Complex.mul_cpow_ofReal_nonneg`).
- **`eqgTerm_prime_pow`** — the local term *is* the corpus's `qBinomialTerm (eqgNome σ p) (p^{-w})`,
  via `Complex.natCast_cpow_natCast_mul` and `Complex.cpow_nat_mul`.
- `norm_natCast_cpow_lt_one`, **`eqgTerm_local_hasSum`** — the local Euler factor is
  `(p^{-w}; q_p)_∞⁻¹`, by the complex q-binomial theorem.
- **`eqgDirichlet_eulerProduct`** — for `Re w > 1`,
  `HasProd (fun p => (p^{-w}; q_p)_∞⁻¹) (∑' m, eqgTerm σ w m)`.

This is the analytic core of (EQG.11)/(EQG.12): at `w = σ(1+s)` the left side is the prime product
of the q-Gamma denominators and the right side is the Dirichlet series of (EQG.12).

`#print axioms` on `eqgDirichlet_eulerProduct`, `eqgTerm_local_hasSum`, `summable_norm_eqgTerm` and
`eqgTerm_prime_pow` reports only `propext`, `Classical.choice`, `Quot.sound`.

Next (step 2b): identify `(q_p^{1+s}; q_p)_∞` with `qDenomProduct (eqgNome σ p) (1+s)` (the corpus's
analytic q-Gamma denominator) and assemble
`Γ_{q_p}(1+s) = (1−q_p)^{-s}(q_p;q_p)_∞/(q_p^{1+s};q_p)_∞`, then multiply the three prime products —
`ζ(σ)^s` from the first factor (mathlib's `riemannZeta` Euler product at the real point `σ`), `C_σ`
from the second (already certified as `eqgConst_hasProd`), and the Dirichlet series from the third.
The only new analytic input needed is `((x^a : ℝ) : ℂ)^w = (x:ℂ)^(a·w)` for `x > 0` and real `a`,
which is a two-line `Complex.log_ofReal`/`Real.log_rpow` computation.

### Step 2 is done — Theorem 4.1 is certified

`GaloisForLFunctions/HTGeometry/EulerQGammaLocalFactor.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,547-job build green).

- `ofReal_rpow_cpow` (`((x^a : ℝ) : ℂ)^w = (x:ℂ)^(a·w)` for `x > 0` and real `a`, by
  `Complex.cpow_def_of_ne_zero` and `Real.log_rpow`) and **`eqgNome_cpow`**
  (`(q_p)^w = p^{−σw}`), the bridge between the local nome and the arithmetic exponent.
- **`qGammaOn_eqgNome_factor`** — the local response splits exactly:
  `Γ_{q_p}(1+s) = (1−q_p)^{−s} · (q_p;q_p)_∞ · (p^{−σ(1+s)}; q_p)_∞⁻¹`, using the corpus's
  `qDenomProduct_eq`.
- The unit product: `summable_eqgQ_primes`, **`abs_log_one_sub_le`** (`|log(1−q)| ≤ 2q` for
  `q ≤ 1/2`, the same `exp(−2x) ≤ 1−x` brick read through `Real.le_log_iff_exp_le`),
  `summable_log_one_sub`, `eqgLogUnit`, `hasProd_one_sub`, `hasProd_one_sub_complex`.
- **`exp_eqgLogUnit_eq_zeta_inv`** — the unit prime product is `ζ(σ)⁻¹`, by comparing the corpus
  product with mathlib's `riemannZeta_eulerProduct_hasProd` through uniqueness of limits; then
  `zeta_eq_exp`, `zeta_cpow`, and **`hasProd_one_sub_cpow`**:
  `HasProd (fun p => (1−q_p)^{−s}) (ζ(σ)^s)` — the first prime product *is* `ζ(σ)^s`, with no
  branch ambiguity because every factor is a positive real.
- **`eqgResponse_hasProd`** — **Theorem 4.1, equation (EQG.11)**: for `Re(σ(1+s)) > 1`
  (equation (EQG.10)),

  `HasProd (fun p => Γ_{q_p}(1+s)) (ζ(σ)^s · C_σ · ∑'_m m^{−σ(1+s)}/∏_p (q_p;q_p)_{v_p(m)})`,

  by multiplying the three prime products: `ζ(σ)^s`, the certified `eqgConst_hasProd`, and the
  certified `eqgDirichlet_eulerProduct`.
- **Equations (EQG.8), (EQG.9), (EQG.12)**: `eqgTerm_eqgExponent` and
  `eqgDirichlet_eq_lawTransform` — the shifted arithmetic term is the unnormalised law times
  `m^{−σs}`, i.e. exactly `P_σ(m)·e^{sX_σ(m)}/C_σ` with `X_σ = log ζ(σ) − σ log M`, so the Dirichlet
  series of (EQG.12) is the exponential response of the random-integer law.

`#print axioms` on `eqgResponse_hasProd`, `hasProd_one_sub_cpow`, `exp_eqgLogUnit_eq_zeta_inv`,
`qGammaOn_eqgNome_factor`, `ofReal_rpow_cpow`, `eqgTerm_eqgExponent` and
`eqgDirichlet_eq_lawTransform` reports only `propext`, `Classical.choice`, `Quot.sound`.

Remaining on this card: steps 3–7 (Theorems 5.1, 6.1, 7.1, 8.1, 9.1).  The next step is the
`ζ(σ(1+s+k))` ladder: interchange the two prime/occupation products in
`(p^{−σ(1+s)}; q_p)_∞⁻¹ = ∏_{k≥0}(1 − p^{−σ(1+s+k)})⁻¹` and apply
`riemannZeta_eulerProduct_hasProd` at each `σ(1+s+k)`, which turns `eqgResponse_hasProd` into the
zeta-ladder form and then feeds the meromorphic continuation and the translation law (EQG.13).

### Step 3 is done — the translation law and the source normalisation

`GaloisForLFunctions/HTGeometry/EulerQGammaTranslation.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,548-job build green).

The zeta ladder is not needed for the translation law: **Jackson's q-Pochhammer shift does the
whole job**.  Read at `a = p^{-w}`, `q = p^{-σ}`, the corpus's `qPochhammerInf_shift` factors the
local Euler factor of the arithmetic Dirichlet series,

`(p^{-w};q_p)_∞⁻¹ = (1 − p^{-w})⁻¹ · (p^{-(w+σ)};q_p)_∞⁻¹`  (`eqgLocalFactor_shift`),

and multiplying over the primes turns the first factor into `ζ(w)` by mathlib's Euler product.

- `eqgDirichlet σ w = ∑' m, eqgTerm σ w m` and **`eqgDirichlet_shift`** —
  `D_σ(w) = ζ(w)·D_σ(w+σ)` for `Re w > 1`, by uniqueness of limits against the two Euler products.
- **`eqgResponse`** (equation (EQG.9)) with `eqgResponse_hasProd'`: the prime product of local
  q-Gamma responses converges to it on the chamber.
- **`eqgResponse_translation`** — **Theorem 5.1, equation (EQG.13)**:

  `F_σ(s+1) = ζ(σ)/ζ(σ(1+s)) · F_σ(s)`.

- `eqgTerm_sigma`, `eqgDirichlet_sigma` (`D_σ(σ)` is the total mass of the arithmetic weight), and
  **equation (EQG.14)**: `eqgResponse_zero : F_σ(0) = 1` and `eqgResponse_one : F_σ(1) = 1` — the
  second by the translation law at `s = 0`, since `ζ(σ)/ζ(σ) = 1`.
- **Equation (EQG.15)**: `summable_eqgTerm`, `eqgTiltTerm` and **`eqgTilt_hasSum_one`** —
  `∑_m P_σ(m)·ζ(σ)·m^{-σ} = 1`, i.e. the exponential intervention `e^{X_σ} = ζ(σ)M^{-σ}` is
  already a probability density and needs no fitted scalar correction.

`#print axioms` on `eqgResponse_translation`, `eqgDirichlet_shift`, `eqgResponse_zero`,
`eqgResponse_one`, `eqgTilt_hasSum_one` and `eqgLocalFactor_shift` reports only `propext`,
`Classical.choice`, `Quot.sound`.

Remaining on this card: the meromorphic continuation clause of Theorem 5.1 (the `∏_{k≥0}
ζ(σ(1+s+k))` ladder, which needs the interchange of the prime and occupation products and the
normal convergence of the far-right tail), then Theorems 6.1, 7.1, 8.1 and 9.1.  Note that the
translation law (EQG.13) — the input to Theorem 6.1's divisor transgression — is now certified in
the chamber without any of that machinery; what the ladder adds is the *domain* on which the
divisor statement can be read.

### Step 4 is done — the zeta ladder

`GaloisForLFunctions/HTGeometry/EulerQGammaLadder.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,549-job build green).

The ladder needs **no interchange of the prime and occupation products**: iterating the certified
shift law `D_σ(w) = ζ(w)·D_σ(w+σ)` gives the exact finite ladder, and the far-right Dirichlet
series tends to one.

- `eqgTailBase`, `summable_eqgTailBase`, `eqgTailConst` (the comparison constant `∑_{m≥2} m^{-2}`)
  and `rpow_le_two_rpow`.
- **`eqgWeightRe_tail_le`** — for `x ≥ 2` and `m ≥ 2`,
  `eqgWeightRe σ x m ≤ E·2^{-(x-2)}·m^{-2}` with `E = exp(4∑_n n^{-σ})`: the same uniform
  denominator bound, now split as `m^{-x} = m^{-2}·m^{-(x-2)} ≤ m^{-2}·2^{-(x-2)}`.
- **`norm_eqgDirichlet_sub_one_le`** — `‖D_σ(v) − 1‖ ≤ E·2^{-(Re v − 2)}·B` for `Re v ≥ 2`, by
  subtracting the `m = 1` term as a `HasSum` and bounding the rest.
- **`tendsto_eqgDirichlet_shift_one`** — `D_σ(w + Nσ) → 1` as `N → ∞`.
- **`eqgDirichlet_ladder_step`** — the exact finite ladder
  `D_σ(w) = (∏_{k<N} ζ(w+kσ))·D_σ(w+Nσ)`, by induction on `N`.
- **`eqgDirichlet_ladder`** — **equation (EQG.11), ladder form**: the partial products
  `∏_{k<N} ζ(w+kσ)` converge to `D_σ(w)` for `Re w > 1`; and **`eqgResponse_ladder`**, the same
  statement for the response:

  `F_σ(s) = ζ(σ)^s · C_σ · ∏_{k≥0} ζ(σ(1+s+k))`.

`#print axioms` on `eqgDirichlet_ladder`, `eqgResponse_ladder`, `tendsto_eqgDirichlet_shift_one`,
`norm_eqgDirichlet_sub_one_le` and `eqgDirichlet_ladder_step` reports only `propext`,
`Classical.choice`, `Quot.sound`.

**State of the card.**  Certified: Theorem 3.1 (EQG.6, EQG.7), Theorem 4.1 (EQG.8–EQG.12 in both
the prime-product and the ladder form), and Theorem 5.1's translation law and normalisation
(EQG.13, EQG.14, EQG.15).  Five modules: `EulerQGammaGlobalLaw`, `EulerQGammaDirichlet`,
`EulerQGammaLocalFactor`, `EulerQGammaTranslation`, `EulerQGammaLadder`.

Remaining: the meromorphic-continuation clause of Theorem 5.1 — the tail
`∏_{k≥K} ζ(σ(1+s+k))` is holomorphic and zero-free on compacts (the corpus already runs exactly
this pattern in `QGammaAnalytic` through `HasProdLocallyUniformlyOn`), leaving finitely many
meromorphic factors — and then Theorems 6.1 (the order transgression, which only has content
outside the chamber and so waits on the continuation), 7.1, 8.1 and 9.1.

### Step 5 is done — the Dirichlet series is analytic on the chamber

`GaloisForLFunctions/HTGeometry/EulerQGammaAnalytic.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,550-job build green).

- `eqgHalf x₀ = {Re w > x₀}` with `isOpen_eqgHalf`, `convex_eqgHalf`, and `log_natCast_nonneg`.
- **`hasDerivAt_eqgTerm`** — each arithmetic term differentiates to `−log m · m^{-w}/den`, through
  `Complex.hasStrictDerivAt_const_cpow` composed with negation and divided by the constant
  denominator.
- `norm_eqgTermDeriv` (`‖·‖ = log m · eqgWeightRe σ (Re w) m`), `eqgDerivBound`,
  `norm_eqgTermDeriv_le`, and **`summable_eqgDerivBound`** — the differentiated series is dominated
  by `log m · E · m^{-x₀}`, summable for `x₀ > 1` because `log m ≤ m^δ/δ`
  (`Real.log_le_rpow_div`) with `δ = (x₀−1)/2`, leaving the exponent `x₀ − δ = (x₀+1)/2 > 1`.
- **`hasDerivAt_eqgDirichlet`** — term-by-term differentiation on each `eqgHalf x₀`, through
  mathlib's `hasDerivAt_tsum_of_isPreconnected`; then `differentiableOn_eqgDirichlet` and
  **`analyticAt_eqgDirichlet`**: `D_σ` is analytic at every `w` with `Re w > 1`.

`#print axioms` on `analyticAt_eqgDirichlet`, `hasDerivAt_eqgDirichlet`, `summable_eqgDerivBound`
and `hasDerivAt_eqgTerm` reports only `propext`, `Classical.choice`, `Quot.sound`.

**Architecture of the remaining continuation.**  With the ladder step and this analyticity, the
continued response is
`F_σ^K(s) = ζ(σ)^s · C_σ · (∏_{k<K} ζ(σ(1+s+k))) · D_σ(σ(1+s+K))`,
which agrees with `eqgResponse` on the chamber (by `eqgDirichlet_ladder_step`), is independent of
`K` where two choices are both admissible (by `eqgDirichlet_shift`), is defined for *every* `s` once
`K` is large enough, and is meromorphic there because the last factor is analytic
(`analyticAt_eqgDirichlet`) and the first is entire (`ζ(σ)` is a nonzero constant).

**One mathlib gap identified.**  The finitely many factors `ζ(σ(1+s+k))` need
`MeromorphicAt riemannZeta z` for every `z`, and mathlib does **not** have it: it has
`differentiableAt_riemannZeta (hs : s ≠ 1)` and `riemannZeta_residue_one` but no meromorphy
statement.  Away from `1` this is `DifferentiableOn` on the open set `{1}ᶜ` upgraded to
`AnalyticAt`; at `1` the honest route is `n = 2` — `(z−1)²·ζ(z)` is bounded near `1` by the residue
limit, so `Mathlib/Analysis/Complex/RemovableSingularity.lean`'s
`differentiableOn_update_limUnder_of_bddAbove` makes it analytic there, and its *actual* value at
`1` is already `0`, matching the extension.  That is the next module to build.

### Step 6 is done — Theorem 5.1 is fully certified

`GaloisForLFunctions/HTGeometry/EulerQGammaContinuation.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,552-job build green).

**The corpus already owned the zeta meromorphy.**  `HTGeometry/ZetaJetFreeness.lean` carries
`meromorphicAt_riemannZeta_one` (through `RHTower.zetaResidueUnit`), and mathlib carries
`analyticOn_riemannZeta : AnalyticOnNhd ℂ riemannZeta {1}ᶜ`; together they give
**`meromorphicAt_riemannZeta : ∀ z, MeromorphicAt riemannZeta z`** in three lines.  The
removable-singularity module scoped in the previous entry was therefore unnecessary — the gap was
in mathlib, not in this corpus.

- **`meromorphicAt_comp_affine`** — meromorphy is preserved by an affine substitution `z ↦ az+b`
  with `a ≠ 0`; proved from the definition, since `(z−s)ⁿ = a^{-n}(φz − φs)ⁿ`.  mathlib has no
  composition lemma for `MeromorphicAt`, so this is new infrastructure.
- `eqgArg σ K s = σ(1+s)+Kσ` with `eqgArg_affine`, and **`eqgCont σ K s`** — the response with the
  zeta ladder cut after `K` factors.
- **`eqgCont_eq_response`** — the cut ladder computes the response on the chamber (from
  `eqgDirichlet_ladder_step`), and **`eqgCont_succ`** — raising the cut changes nothing where both
  are admissible (from `eqgDirichlet_shift`).
- `analyticAt_zeta_sigma_cpow` (the factor `ζ(σ)^s` is entire, since `ζ(σ)` is a nonzero constant),
  `meromorphicAt_zeta_ladder_factor` (each `ζ(σ(1+s+k))` is meromorphic in `s`, by the affine
  composition lemma), `analyticAt_eqgDirichlet_arg` (the tail is analytic, by
  `analyticAt_eqgDirichlet`), hence **`meromorphicAt_eqgCont`**.
- `exists_admissible_cut` — every `s` becomes admissible for large `K` — and the capstone
  **`eqgResponse_meromorphic_continuation`**: for every `s : ℂ` there is a `K` with
  `MeromorphicAt (eqgCont σ K) s`, and that cut agrees with `eqgResponse σ` on the whole chamber.
  **This is Theorem 5.1's continuation clause.**
- **`eqgCont_translation`** — an *unconditional* identity, valid at every `s` and every `K`:

  `ζ(σ)·F^{K+1}_σ(s) = ζ(σ(1+s))·F^K_σ(s+1)`.

  On the chamber this is (EQG.13); off it, it is the translation law of the meromorphic
  continuation, and it is the exact input to Theorem 6.1's divisor transgression.

`#print axioms` on `eqgResponse_meromorphic_continuation`, `meromorphicAt_eqgCont`,
`eqgCont_eq_response`, `eqgCont_succ`, `meromorphicAt_comp_affine` and `eqgCont_translation`
reports only `propext`, `Classical.choice`, `Quot.sound`.

**Theorem 5.1 is now complete** (continuation, translation law, normalisation).  Certified so far:
Theorems 3.1, 4.1, 5.1.  Remaining: Theorem 6.1 (take `meromorphicOrderAt` of
`eqgCont_translation`, which needs the behaviour of the order under `s ↦ s+1` and under the affine
substitution — the same shape as `meromorphicAt_comp_affine`), then 7.1, 8.1 and 9.1.

### Step 7 is done — Theorem 6.1, the divisor transgression

`GaloisForLFunctions/HTGeometry/EulerQGammaDivisor.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,553-job build green).

The unconditional `eqgCont_translation` is an identity of *functions*, so taking meromorphic orders
at a point converts it directly into the divisor transgression.

- `tendsto_affine_nhdsWithin` and **`meromorphicOrderAt_comp_affine`** — the meromorphic order is
  invariant under an affine substitution `z ↦ az+b`, `a ≠ 0`.  mathlib has no such lemma; it is
  proved here from the `meromorphicOrderAt_eq_int_iff` normal form, by transporting the witness
  `g` to `z ↦ aⁿ·g(az+b)` and using `(az+b) − (as+b) = a(z−s)`.  The `⊤` case is the pullback of
  the eventual vanishing along the same substitution.
- `meromorphicAt_zeta_exponent`, **`meromorphicOrderAt_zeta_exponent`**
  (`ord_a (s ↦ ζ(σ(1+s))) = ord_{σ(1+a)} ζ`), `meromorphicAt_eqgCont_succ_arg` and
  **`meromorphicOrderAt_eqgCont_succ_arg`** (`ord_a (s ↦ F(s+1)) = ord_{a+1} F`) — the two
  substitutions the transgression needs, both instances of the affine lemma.
- `eqgArg_succ_shift` (`eqgArg σ K (a+1) = eqgArg σ (K+1) a`: one admissibility hypothesis serves
  both sides) and the capstone **`eqgCont_order_transgression`** — **Theorem 6.1, equation
  (EQG.17)**:

  `ord_a F^{K+1}_σ = ord_{σ(1+a)} ζ + ord_{a+1} F^K_σ`,

  i.e. `ord_{a+1} F_σ − ord_a F_σ = −ord_{σ(1+a)} ζ`, the exact Cartier-divisor transgression
  `T*div(F_σ) − div(F_σ) = −φ_σ*div(ζ)` read pointwise.

`#print axioms` on `eqgCont_order_transgression`, `meromorphicOrderAt_comp_affine`,
`meromorphicOrderAt_zeta_exponent` and `meromorphicOrderAt_eqgCont_succ_arg` reports only
`propext`, `Classical.choice`, `Quot.sound`.

**State of the card.**  Certified: **Theorems 3.1, 4.1, 5.1 and 6.1** — equations (EQG.6), (EQG.7),
(EQG.8)–(EQG.12) in both the prime-product and ladder forms, (EQG.13), (EQG.14), (EQG.15),
(EQG.16)/(EQG.17), plus the meromorphic continuation.  Eight modules: `EulerQGammaGlobalLaw`,
`EulerQGammaDirichlet`, `EulerQGammaLocalFactor`, `EulerQGammaTranslation`, `EulerQGammaLadder`,
`EulerQGammaAnalytic`, `EulerQGammaContinuation`, `EulerQGammaDivisor`.

Remaining: (EQG.18) — the clean landing `ord_{a_ρ} F_σ = m_ρ` with `F_σ(a_ρ+1) ≠ 0,∞` at a
nontrivial zero `ρ`, which needs the zero-freeness of every ladder factor at `a_ρ+1` (all arguments
have real part `Re ρ + σ(1+k) > 1`, so `riemannZeta_ne_zero_of_one_lt_re` applies, and the tail is
nonzero because `D_σ(v) → 1`); then Theorems 7.1 (hypertranscendence, which can now use
`eqgCont_translation` together with the corpus's `hypertranscendental_gamma`), 8.1 (the
`L²(ℕ_{>0}, P_σ)` observer, the same shape as the already-certified `ConstitutiveQGammaProcess`
GNS layer) and 9.1 (the genus-one renormalisation).

### Step 8 is done — Theorem 6.1 is complete, including the clean landing (EQG.18)

`GaloisForLFunctions/HTGeometry/EulerQGammaLanding.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,555-job build green).

- `meromorphicOrderAt_eq_zero_of_analytic` — a nonvanishing analytic germ has order zero.
- **`eqgDirichlet_ne_zero`** — the arithmetic Dirichlet series is nonvanishing on the whole
  chamber.  The infinite product could a priori vanish; the finite ladder settles it: choose `N`
  with `D_σ(v+Nσ)` inside the unit ball around `1` (so nonzero), and then
  `D_σ(v) = (∏_{k<N} ζ(v+kσ))·D_σ(v+Nσ)` is a product of nonzero factors, every zeta argument
  having real part `> 1`.
- `analyticAt_zeta_affine`, `zeta_sigma_cpow_ne_zero`, **`analyticAt_eqgCont`** and
  **`eqgCont_ne_zero`** — the cut ladder is analytic and nonvanishing at any point where all its
  arguments sit in the zero-free half-plane.
- `eqgLandingPoint σ ρ = ρ/σ − 1` with **`eqgExponent_landingPoint`** (`σ(1+a_ρ) = ρ` exactly),
  `eqgExponent_landingPoint_succ`, `re_landing_gt_one` (`Re(ρ + (k+1)σ) > 1` whenever `Re ρ > 0`)
  and `re_landing_arg_gt_one`.
- **`eqgCont_order_at_zeta_zero`** — **equation (EQG.18)**: for any `ρ` with `Re ρ > 0`,

  `ord_{a_ρ} F_σ = ord_ρ ζ`,

  the full multiplicity of the zeta zero landing at `a_ρ = ρ/σ − 1`; and
  **`eqgCont_landing_translate_ne_zero`** — the unit translate `a_ρ+1` is an analytic,
  *nonvanishing* value of the response, which is the `≠ 0, ∞` clause of (EQG.18).

`#print axioms` on `eqgCont_order_at_zeta_zero`, `eqgCont_landing_translate_ne_zero`,
`eqgDirichlet_ne_zero` and `analyticAt_eqgCont` reports only `propext`, `Classical.choice`,
`Quot.sound`.

**State of the card.**  Certified: **Theorems 3.1, 4.1, 5.1 and 6.1 in full** — (EQG.6), (EQG.7),
(EQG.8)–(EQG.12) in both forms, (EQG.13)–(EQG.15), the meromorphic continuation, (EQG.16)/(EQG.17)
and (EQG.18).  Nine modules: `EulerQGammaGlobalLaw`, `EulerQGammaDirichlet`,
`EulerQGammaLocalFactor`, `EulerQGammaTranslation`, `EulerQGammaLadder`, `EulerQGammaAnalytic`,
`EulerQGammaContinuation`, `EulerQGammaDivisor`, `EulerQGammaLanding`.

Remaining: Theorem 7.1 (hypertranscendence of `F_σ`), 8.1 (the `L²(ℕ_{>0}, P_σ)` recurrent
observer) and 9.1 (the genus-one renormalisation and divisor erasure).

### Step 9 is done — the arithmetic observable and Theorem 8.1's compact resolvent

`GaloisForLFunctions/HTGeometry/EulerQGammaObserver.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,556-job build green).

The corpus's `ℓ²` diagonal-operator layer from ULF-QGPRH-1 is reusable verbatim — `lpDiagCLM` and
`isCompactOperator_lpDiagCLM` are stated for `QGammaSpace = lp (fun _ : ℕ => ℂ) 2`, which is also
the model for `L²(ℕ_{>0}, P_σ)`.

- `eqgZetaReal σ = exp(−∑_p log(1−q_p))` with `eqgZetaReal_pos` and **`ofReal_eqgZetaReal`**
  (`(ζ(σ) : ℂ)` is the cast of this positive real, from `zeta_eq_exp`), so the real logarithm
  `log ζ(σ)` is available without any real-variable zeta theory.
- **Equation (EQG.8)**: `eqgObservable σ m = log ζ(σ) − σ·log m`, and **`exp_eqgObservable`** —
  its exponential response is exactly `ζ(σ)^s·m^{-σs}`, the factor that turns the arithmetic
  Dirichlet series into the exponential response of the random-integer law.
- **`tendsto_eqgObservable_atBot`** — the spectral values run off to `−∞`.
- `eqgResolventEntry σ m = (X_σ(m) − i)⁻¹` with `one_le_norm_eqgObservable_sub_I`,
  `eqgResolventEntry_bound`, **`eqgResolventEntry_mul`** (the resolvent inverts `X_σ − i`
  coordinatewise) and `tendsto_norm_eqgResolventEntry`; then `eqgResolvent` and the capstone
  **`isCompactOperator_eqgResolvent`** — **Theorem 8.1's compact-resolvent clause**, in the only
  form mathlib can state it (there is no unbounded self-adjoint operator theory), exactly as the
  sibling clause was certified for ULF-QGPRH-1.

`#print axioms` on `isCompactOperator_eqgResolvent`, `exp_eqgObservable`, `eqgResolventEntry_mul`
and `tendsto_eqgObservable_atBot` reports only `propext`, `Classical.choice`, `Quot.sound`.

**State of the card.**  Ten modules; certified: Theorems 3.1, 4.1, 5.1, 6.1 in full, and Theorem
8.1's operator clause.  Remaining: Theorem 8.1's GNS/recurrence clause (the cyclic vector
`Ω = (√P_σ(m))`, its orbit, the characteristic function, and the compact-group return-time
argument — structurally the same as the certified `qOmega`/`qOrbit`/`exists_qOrbit_near_qOmega`
layer, with the arithmetic atoms in place of the geometric ones), Theorem 7.1 (hypertranscendence
of `F_σ`, which needs a differential-algebra closure layer the corpus does not yet have — DA under
affine substitution, products and quotients — plus the hypertranscendence of `ζ` from the
functional equation and the certified `hypertranscendental_gamma`), and Theorem 9.1 (the genus-one
renormalisation).

### Step 10 is done — Theorem 8.1's GNS and recurrence clauses

`GaloisForLFunctions/HTGeometry/EulerQGammaGNS.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,557-job build green).

`L²(ℕ_{>0}, P_σ)` is modelled by the corpus's `QGammaSpace = lp (fun _ : ℕ => ℂ) 2`.

- `summable_eqgMass`, `eqgSqrt_memℓp`, `eqgSqrt_memℓp'`, and the cyclic vector
  **`eqgOmega σ = (√P_σ(m))`**; `norm_eqgPhase` and the orbit **`eqgOrbit σ t`** (multiplication by
  the phases `exp(i t X_σ(m))`).
- **`eqgCharProc`** — the characteristic function of the random-integer law — with
  `eqgCharProc_hasSum`, **`eqgCharProc_eq_inner`** (it *is* the cyclic matrix coefficient
  `⟪Ω, U_tΩ⟫`) and **`eqgCharProc_eq_response`** — **equation (EQG.9) in characteristic form**:
  `C_σ(t) = F_σ(it)`, obtained by pushing `exp_eqgObservable` through the certified Dirichlet
  transform.
- `eqgOrbit_sub_eqgOmega_apply`, `norm_eqgOrbit_sub_eqgOmega_sq`, `eqgOrbitDiff_le_four`,
  `eqgOrbitDiff_summable`, and **`exists_eqgOrbit_near_eqgOmega`** — **Theorem 8.1's recurrence
  clause**: for every `ε > 0` and every `M` there is an integer time `m ≥ M` with
  `‖U_mΩ − Ω‖ < ε`.  Finitely many phases are returned simultaneously close to `1` by
  `exists_pow_mem_of_compactSpace` in the torus `Fin (N+1) → Circle`, and the tail mass beyond `N`
  is below `ε²/8`.

Only nonnegativity of the masses is used, so the fact that `P_σ(0) = 0` (the integer `0` carries no
mass) is harmless.

`#print axioms` on `exists_eqgOrbit_near_eqgOmega`, `eqgCharProc_eq_inner`,
`eqgCharProc_eq_response` and `norm_eqgOrbit_sub_eqgOmega_sq` reports only `propext`,
`Classical.choice`, `Quot.sound`.

**State of the card.**  Eleven modules.  Certified: **Theorems 3.1, 4.1, 5.1, 6.1 and 8.1** —
(EQG.6)–(EQG.18) together with the meromorphic continuation, the compact resolvent, the GNS matrix
coefficient and the recurrence.

Remaining: Theorem 7.1 (hypertranscendence of `F_σ`) and Theorem 9.1 (genus-one renormalisation and
divisor erasure).  Theorem 7.1 is the one that still needs genuinely new theory: a
differential-algebra closure layer (DA under affine substitution, product and quotient), which the
corpus does not have, plus the hypertranscendence of `ζ` from the functional equation and the
certified `hypertranscendental_gamma`.

### Step 11 is done — the genus-one exchange (Theorem 9.1, algebraic core)

`GaloisForLFunctions/HTGeometry/EulerQGammaGenusOne.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,559-job build green).

The corpus's `EulerQGammaFiniteProcess` already carried the unconditional algebraic identity
`eulerQGamma_genusOne_local_exchange`,
`(1−x)e^{−q+(1−q)x}·E₁(q) = (1−q)·E₁(x)·e^{−qx}` with `E₁(z) = (1−z)e^z`.  What was missing was
its q-Gamma reading; that is now supplied.

- **Equation (EQG.20)**: `eqgActivation q s = q(s−1) + q^{1+s}`, with `qcpow_succ` and
  **`eqgActivation_diff`** — the counterterm increment
  `ℓ_q(s) − ℓ_q(s+1) = −q + (1−q)q^{1+s}`, exactly the exponent in the corpus identity.
- **Equation (EQG.21), local factor**: `eqgRenormLocal q s = Γ_q(1+s)·e^{−ℓ_q(s)}`.
- **`eqgRenormLocal_exchange`** — **equation (EQG.24) per prime**:

  `R_q(s+1)·E₁(q) = R_q(s)·E₁(q^{1+s})·e^{−q·q^{1+s}}`,

  proved by cross-multiplying Jackson's functional equation (so no division by `1−q^{1+s}` is
  needed), substituting the counterterm increment, and applying the corpus's algebraic exchange;
  the final cancellation is by `1 − q ≠ 0` alone.  Reading it as a ratio, the translation factor is
  `E₁(p^{-z})/E₁(p^{-σ})·e^{−p^{-(σ+z)}}` — a genus-one unit times a prime-zeta exponential,
  carrying **no divisor**.
- **`eqgRenormLocal_exchange_finset`** — the same over any finite set of primes, which is the
  finite-prime form of the erasure statement.

`#print axioms` on `eqgRenormLocal_exchange`, `eqgRenormLocal_exchange_finset` and
`eqgActivation_diff` reports only `propext`, `Classical.choice`, `Quot.sound`.

**State of the card.**  Twelve modules.  Certified: **Theorems 3.1, 4.1, 5.1, 6.1, 8.1** in full,
and the algebraic core of **9.1**.  Remaining on 9.1: the analytic half — normal convergence of the
infinite product (EQG.21) on the half-plane (EQG.22) and its zero-freeness, which needs the
`O(q²) + O(q^{2(1+Re s)}) + O(q^{2+Re s})` expansion of `log Γ_q(1+s) − ℓ_q(s)` from (EQG.25) and
the corresponding prime sums; and then the passage of the per-prime exchange to the infinite
products `E_1(z)`, `E_1(σ)` and `e^{−P(σ+z)}`.  Remaining overall: Theorem 7.1
(hypertranscendence), which still needs a differential-algebra closure layer plus the
hypertranscendence of `ζ`.

### Frontier note (2026-08-10) — what Theorems 7.1 and 9.1 actually still need

A corpus audit for step 12 turned up much more than expected, and sharpens both remaining items.

**Already owned by the corpus, contrary to the earlier entry:**

- **`RHTower/ZetaHypertranscendental.lean` : `hypertranscendental_riemannZeta`** — the
  hypertranscendence of `ζ` is *already certified*.  The card's own §7 argument (functional
  equation plus Hölder for `Γ`) does not need to be redone.
- `HTGeometry/DifferentiallyAlgebraicInvariance.lean` — translation invariance
  (`differentiallyAlgebraic_comp_add_const_iff`, `hypertranscendental_comp_add_const_iff`),
  scaling invariance, and value-scaling invariance (`DifferentiallyAlgebraic.const_mul`,
  `hypertranscendental_const_mul_iff`).
- `HTGeometry/ArgumentScalingInvariance.lean` — the *unconditional* scaling invariance
  `differentiallyAlgebraic_comp_const_mul_iff_uncond` and `hypertranscendental_gamma_affine`.
- `HTGeometry/AnalyticJetFieldBridge.lean` — `differentiallyAlgebraic_mul`,
  `differentiallyAlgebraic_add`, `differentiallyAlgebraic_sub`, `differentiallyAlgebraic_pow`,
  for **entire** functions, through the `meroField` differential-field bridge.

**So Theorem 7.1 reduces to exactly two named gaps.**  From the certified unconditional identity
`eqgCont_translation`, `ζ(σ)·F^{K+1}_σ(s) = ζ(σ(1+s))·F^K_σ(s+1)`, assuming `F_σ` differentially
algebraic makes the left side DA (`DifferentiallyAlgebraic.const_mul`) and `F^K_σ(·+1)` DA
(translation invariance); the contradiction with `hypertranscendental_riemannZeta` then follows by
argument scaling — *provided* one can divide.  The two missing lemmas are:

1. **DA is closed under reciprocal.**  If `P(z, f, …, f⁽ⁿ⁾) ≡ 0` and `g = 1/f`, then every
   `f⁽ʲ⁾` is an explicit rational function of `g, g', …, g⁽ʲ⁾`; substituting and clearing
   denominators gives a nonzero differential polynomial in `g`.  Elementary and finite, but a real
   induction (the numerators are the Faà-di-Bruno-type polynomials).
2. **The product/quotient closure for meromorphic, not merely entire, functions.**  The corpus's
   bridge is stated for `AnalyticOnNhd ℂ f univ`; `ζ` and `F_σ` have poles.  Either the bridge is
   re-run on a pole-free open connected `U`, or the corpus's `DifferentiallyAlgebraic` predicate is
   given its off-pole variant (the same move `DigammaHypertranscendental` already makes for `ψ`).

**Theorem 9.1** needs only its analytic half: normal convergence of `∏_p Γ_{q_p}(1+s)e^{−ℓ_{p,σ}(s)}`
on `Re s > 1/(2σ) − 1`.  The cleanest Lean route avoids logarithms entirely — bound
`‖R_p(s) − 1‖` directly by `C·q_p²`-type terms and apply the multipliability criterion the corpus
already uses (`tprod_one_add_ne_zero_of_summable`) — but it does require an explicit expansion of
`Γ_q(1+s)` to second order in `q`, which is the one genuinely new estimate.  The algebraic identity
that this convergence is *for* — the divisor erasure — is already certified per prime and over
finite prime sets (`eqgRenormLocal_exchange`, `eqgRenormLocal_exchange_finset`).

Repo lint reports no errors in any `EulerQGamma*` module; the universal-law-field umbrella builds
green at 11,559 jobs.

### Step 13 — the reciprocal jet polynomials (first half of gap 1 for Theorem 7.1)

`GaloisForLFunctions/HTGeometry/ReciprocalJetPolynomials.lean`, wired through
`GaloisForLFunctions.HTGeometry.UniversalLawField` (11,561-job build green).

Gap 1 of the previous entry — *DA is closed under reciprocal* — rests on the jet identity
`f⁽ʲ⁾·g^{j+1} = A_j(g, g', …, g⁽ʲ⁾)` for `f = 1/g`.  This module builds the polynomial side of it.

- **`pderiv_comm`** — partial derivations of `MvPolynomial` commute.  mathlib's
  `Algebra/MvPolynomial/PDeriv.lean` has no such lemma, so it is proved here by the
  `induction_on` recursion, the multiplicative case reducing to `pderiv a (Pi.single b 1 c) = 0`.
- **`jetShiftDeriv`** — the jet derivation `X_i ↦ X_{i+1}` at a fixed arity `Fin (N+2)`,
  truncated at the top variable.  Fixing the arity avoids all `Fin`-cast juggling; the recursion is
  only ever run up to `j ≤ N`, so the truncation is invisible.
- **`recipNum`** — the reciprocal numerators `A_0 = 1`,
  `A_{j+1} = D(A_j)·X₀ − (j+1)·A_j·X₁`, with `recipNum_zero` and `recipNum_succ`.  This is the same
  shape as the `qIncrNum` recursion of ULF-QGPRH-1, which is a good sign: both come from
  differentiating a quotient with a power denominator.
- **`pderiv_jetShiftDeriv_top`** and **`pderiv_recipNum_top`** — the support bookkeeping: `A_j`
  involves no variable above `X_j`.  This is exactly what lets the jet chain rule
  (`hasDerivAt_mvEval_jet`, already corpus-owned) close inside the fixed arity, since the spurious
  top-variable term of the chain rule is killed by `pderiv_{N+1} A_j = 0`.

`#print axioms` on `pderiv_comm`, `pderiv_recipNum_top` and `pderiv_jetShiftDeriv_top` reports only
`propext`, `Classical.choice`, `Quot.sound`.

Next on this thread: the analytic identity `f⁽ʲ⁾·g^{j+1} = eval (g-jet) (A_j)` by induction on `j`
(differentiate both sides, use `hasDerivAt_mvEval_jet` on the right and the product rule on the
left, then cancel one factor of `g`), then the substitution `y_j ↦ A_j/Y₀^{j+1}` into an
annihilating polynomial together with the involutivity argument for nonvanishing of the result.

### Step 14 — the reciprocal jet identity is proved

`GaloisForLFunctions/HTGeometry/ReciprocalJetPolynomials.lean` (extended), umbrella green at
11,561 jobs.

- **`eval_jetShiftDeriv`** — evaluating the truncated jet derivation on a jet of `g` reproduces the
  full chain-rule sum, because the one spurious top-variable term is killed by
  `pderiv_{last} Q = 0`.
- **`recipNum_eval`** — **the reciprocal jet identity**:

  if `f·g = 1` on an open `U` and both jets differentiate (`HasDerivAt (iteratedDeriv k ·)
  (iteratedDeriv (k+1) · z) z` for every `k` and every `z ∈ U`), then for every `j ≤ N` and every
  `z ∈ U`

  `f⁽ʲ⁾(z)·g(z)^{j+1} = A_j(g(z), g'(z), …, g⁽ᴺ⁺¹⁾(z))`.

  Proved by induction on `j`: the two sides agree on a neighbourhood of `z` (the set is open), so
  their derivatives agree; the left side differentiates by the product and power rules and the
  right by `hasDerivAt_mvEval_jet`; multiplying by `g(z)` and substituting the induction hypothesis
  gives exactly the defining recursion of `A_{j+1}`.  No division is used anywhere — the
  non-vanishing hypothesis turned out to be unnecessary and was dropped, so the identity holds
  wherever `f·g = 1`.

`#print axioms` on `recipNum_eval` and `eval_jetShiftDeriv` reports only `propext`,
`Classical.choice`, `Quot.sound`.

**What remains for gap 1** (DA closed under reciprocal): substitute `y_j ↦ A_j/Y₀^{j+1}` into an
annihilating differential polynomial `P` for `f`, clear the denominator by `Y₀^{(deg P)(N+2)}`, and
show the resulting `Q` is nonzero — the clean argument being that applying the same construction to
`Q` returns `P` times a power of `Y₀`, since `g ↦ 1/g` is an involution.  With that, the divide in
Theorem 7.1's chain (`ζ(σ(1+s)) = ζ(σ)·F^{K+1}(s)/F^K(s+1)`) is licensed, and the remaining
ingredients — `hypertranscendental_riemannZeta`, translation invariance and argument scaling — are
all already corpus-owned.

### Step 15 — reciprocal jet numerators are nonzero

`formal/GaloisForLFunctions/HTGeometry/ReciprocalJetPolynomials.lean` (extended)

Testing the jet identity `f⁽ʲ⁾·g^{j+1} = A_j(g, g′, …)` on the explicit pair `g = exp`,
`f = exp(−·)` at the origin evaluates `A_j` at the all-ones jet to `(−1)ʲ`, so every reciprocal
numerator is a nonzero polynomial.

| Declaration | Statement |
|---|---|
| `iteratedDeriv_cexp` | `iteratedDeriv k exp = exp` |
| `iteratedDeriv_cexp_neg` | `iteratedDeriv k (exp ∘ neg) = (−1)^k · exp ∘ neg` |
| `hasDerivAt_iteratedDeriv_cexp`, `hasDerivAt_iteratedDeriv_cexp_neg` | jet differentiability of the test pair |
| `recipNum_ne_zero` | `j ≤ N → recipNum N j ≠ 0` |

### Step 16 — reciprocal closure of differential algebraicity (gap 1 closed)

`formal/GaloisForLFunctions/HTGeometry/ReciprocalSubstitution.lean`,
`formal/GaloisForLFunctions/HTGeometry/ReciprocalSubstitutionInjective.lean`

The substitution `y_j ↦ A_j/g^{j+1}` is realised as an explicit polynomial map, the single
denominator is cleared by `g^{(n+1)·deg P}`, and the map is proved injective by testing on the
digamma pair `ψ`, `1/ψ` and invoking Hölder's theorem.

| Declaration | Statement |
|---|---|
| `recipWeight`, `recipBound` | monomial weight `∑ⱼ(j+1)αⱼ` and clearing exponent `(n+1)·deg P` |
| `recipWeight_le_recipBound` | the clearing exponent dominates every monomial weight |
| `recipSub` | the substituted differential polynomial, one jet order higher |
| `eval_recipSub` | `recipSub n P (s, g, g′, …) = P(s, f, f′, …)·g^{(n+1)deg P}` wherever `f·g = 1` |
| `digammaUnitSet`, `isOpen_digammaUnitSet`, `digammaUnitSet_nonempty` | the open nonempty locus where `ψ` is analytic and invertible |
| `analyticAt_digammaJetEval` | analyticity of the digamma jet evaluation off the poles |
| `digamma_relation_propagates` | a local digamma relation propagates off all poles |
| `recipSub_eq_zero_iff` | `recipSub n P = 0 → P = 0` |
| `differentiallyAlgebraicOn_of_mul_eq_one` | `f·g = 1` on an open set with `f` DA there ⇒ `g` DA there |
| `differentiallyAlgebraicOn_inv` | DA is closed under inverses of nonvanishing analytic functions |
| `not_differentiallyAlgebraicOn_of_inv` | hypertranscendence transfers to the reciprocal |
| `differentiallyAlgebraic_inv` | global form for nonvanishing entire functions |

### Step 17 — Theorem 7.1: the response is hypertranscendental (COMPLETE)

`formal/GaloisForLFunctions/HTGeometry/DifferentialAlgebraicOnClosure.lean`,
`formal/GaloisForLFunctions/HTGeometry/DifferentialAlgebraicPropagation.lean`,
`formal/GaloisForLFunctions/HTGeometry/EulerQGammaHypertranscendence.lean`

Gap 2 was closed by instantiating the meromorphic jet field bridge at a general domain, and the
assembly then runs exactly as planned: the one-step ladder `D(v) = ζ(v)·D(v+σ)` exhibits
`ζ(σ(1+s))` as `F(s)/F(s+1)`, quotient closure and translation give a differential relation for
the pulled-back zeta function, the relation propagates across the single pole, and undoing the
affine substitution contradicts Hilbert's theorem.

| Declaration | Statement |
|---|---|
| `DifferentiallyAlgebraicOn.comp_add_const` | translation of the argument moves the domain |
| `differentiallyAlgebraicOn_mul` | products, on any open preconnected infinite domain |
| `differentiallyAlgebraicOn_div` | quotients by nonvanishing analytic differentially algebraic functions |
| `analyticAt_jetEval` | a differential relation of an analytic function is analytic |
| `differentiallyAlgebraicOn_mono_of_isPreconnected` | local relations propagate over a preconnected domain |
| `isPreconnected_compl_singleton` | `ℂ ∖ {p}` is preconnected |
| `differentiallyAlgebraic_of_on_compl_singleton` | a relation off one point becomes global after multiplying by `(s − p)` |
| `eqgHalfPlane`, `mem_eqgHalfPlane` | the convergence half plane `Re s > 1/σ − 1` and its exponent form |
| `eqgResponseDirichlet`, `eqgResponseDirichlet_ladder` | the response in the pulled-back variable and its one-step ladder |
| `eqgZetaPullback`, `eqgPolePoint`, `analyticOnNhd_eqgZetaPullback` | the pulled-back zeta function and its single pole |
| `hypertranscendental_eqgZetaPullback` | `s ↦ ζ(σ(1+s))` satisfies no algebraic differential equation |
| `not_differentiallyAlgebraicOn_eqgResponseDirichlet` | the arithmetic Dirichlet response is hypertranscendental on the half plane |
| `eqgUnitFactor`, `differentiallyAlgebraic_eqgUnitFactor` | the prefactor `C·ζ(σ)^s` is differentially algebraic |
| **`not_differentiallyAlgebraicOn_eqgResponse`** | **Theorem 7.1** — the Euler q-Gamma response is hypertranscendental on its convergence half plane |
| `not_differentiallyAlgebraicOn_eqgCont` | the same for every cut of the analytic continuation |

Axiom audit for steps 15–17: `propext, Classical.choice, Quot.sound` only.  Umbrella
`GaloisForLFunctions.HTGeometry.UniversalLawField` green at 11 568 jobs.

**Frontier note (2026-08-10, updated).**  Theorem 7.1 is closed unconditionally; gaps 1 and 2 are
both discharged.  The one remaining item on this card is the analytic half of Theorem 9.1: normal
convergence and zero-freeness of `∏_p Γ_{q_p}(1+s)·e^{−ℓ_{p,σ}(s)}` on `Re s > 1/(2σ) − 1`, which
needs the second-order expansion of `Γ_q(1+s)` in `q` (EQG.25) and the passage of the per-prime
genus-one exchange (`eqgRenormLocal_exchange`, already proved) to the infinite product.
