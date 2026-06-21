I would now put the search target this way:

[
\boxed{
\textbf{A genuine HT detector must detect arithmetic complexity of the divisor, not source geometry of the divisor.}
}
]

Your current notes make that constraint sharp. The phase/holonomy carrier is settled as a completed analytic-continuation / zero-structure detector, not a native hypertranscendence detector; source-quotienting (\xi'/\xi) removes the divisor and leaves only tame data, so it removes exactly the structure carrying the HT content.  The RH wall is geometry — where the zeros sit, equivalently Stieltjes positivity of (y_\rho=-(\rho-\frac12)^{-2}) — while the value/transcendence apex is arithmetic — algebraic relations among ({\gamma_n}), ({S_k}), ({\log p}), and related value families.

So the detector cannot be (\Delta), (D_2), (M_k), (T_k)-positivity, (\kappa_-), source-width tomography, contour charge, or Ward residual. Those are B/C-axis instruments. The new detector must live on the A-axis: **relations among values**.

Here are the strongest candidate directions.

---

## 1. Prime-log Schanuel shell-profile detector

This is the most direct candidate.

Let

[
L_N=(\log p_1,\ldots,\log p_N).
]

For degree (d), height (H), define an exact shell minimum

[
\mathcal M_{N,d}(H)
===================

\min_{\substack{0\ne P\in\mathbb Z[x_1,\ldots,x_N]\
\deg P\le d,\ H(P)\le H}}
|P(L_N)|.
]

A genuine arithmetic detector would not merely ask whether a random search finds a relation. It would study the **height-growth profile** of exact shell minima:

[
H\mapsto \mathcal M_{N,d}(H).
]

If ({\log p}) are algebraically independent, these minima never vanish. The problem is that proving non-vanishing and useful lower bounds is Schanuel-level hard; your notes explicitly identify the algebraic prime-log apex as open, with even the degree-2 rung for (\log 2,\log 3) beyond current reach.

**Why this might be the real detector:** it measures divisor arithmetic through the prime side, not zero geometry. It also directly targets the “missing single Frobenius” gap: the linear floor is known; the algebraic apex is the unknown layer.

**Computational version:** exact meet-in-the-middle shell search, lattice reduction, interval-certified evaluation, and comparison to algebraically dependent controls. Random residual histograms do not count.

---

## 2. Zero-ordinate algebraic shell-profile detector

Instead of ({\log p}), work directly with the zero ordinates

[
\Gamma_N=(\gamma_1,\ldots,\gamma_N).
]

Define

[
\mathcal Z_{N,d}(H)
===================

\min_{\substack{0\ne P\in\mathbb Z[x_1,\ldots,x_N]\
\deg P\le d,\ H(P)\le H}}
|P(\Gamma_N)|.
]

This is the zero-side analogue of the prime-log detector.

**Why plausible:** (\xi)'s hypertranscendence is divisor-encoded. The contrast with (\sin \pi s) is the key mental model: both are order-one entire functions with infinite divisors, but the sine divisor is an arithmetic progression and yields a D-algebraic function; zeta’s divisor appears arithmetically much more rigid/irregular.

**Main risk:** zero ordinates include geometry and arithmetic at once. To make this A-axis rather than B/C-axis, the detector must be invariant under geometric controls: same density, same pair correlation, same seam support, different arithmetic relations.

---

## 3. Seam-value algebraic independence detector

The seam cancellation note gives a concrete value family:

[
S_k=\sum_\rho(\rho-\tfrac12)^{-2k}.
]

The fused seam formula expresses (S_k) as a mixture of archimedean period data, Dirichlet beta / Catalan-family constants, and prime-side derivatives at the seam. The one-wall note says ({S_k}) belongs to the value-axis when we ask about algebraic relations, not positivity.

Define a field tower

[
K_N
===

\mathbb Q\big(
S_1,\ldots,S_N,,
\pi,,
\beta(2),\ldots,\beta(2N),,
(\zeta'/\zeta)^{(1)}(1/2),\ldots,
(\zeta'/\zeta)^{(2N-1)}(1/2)
\big).
]

A detector would measure whether the transcendence degree / algebraic relation complexity of this tower grows with (N).

**Why plausible:** it uses the seam identity but asks a value-arithmetic question, not a source-geometry question.

**Computational version:** relation searches among the (S_k) after subtracting known archimedean pieces; compare to sine, gamma-only, artificial zero sequences, and D-finite / D-algebraic toy functions.

**Main risk:** numerically, this may collapse back to shift/derivative rank unless the detector explicitly measures algebraic relation height, not just matrix rank.

---

## 4. Jet-algebraic nonclosure detector at the seam

If a function is differentially algebraic over (\mathbb C(s)), then some finite jet

[
f,f',\ldots,f^{(n)}
]

satisfies a polynomial relation. For the seam object, one can look at the jet of

[
\frac{\zeta'}{\zeta}
]

at (s=\frac12):

[
J_N
===

\left(
(\zeta'/\zeta)^{(0)}(1/2),
(\zeta'/\zeta)^{(1)}(1/2),
\ldots,
(\zeta'/\zeta)^{(N)}(1/2)
\right).
]

Then define algebraic shell minima

[
\mathcal J_{N,d}(H)
===================

\min_{0\ne P,\ \deg P\le d,\ H(P)\le H}
|P(J_N)|.
]

**Why plausible:** this directly targets differential-algebraic nonclosure, but at the value/arithmetic level, not by quotienting the divisor.

**Why it is hard:** it may reduce to the known shift/derivative-rank detector. The corpus says every structural value-relation invariant tried so far collapses to shift/derivative rank, and finding something not of that type is the moonshot.

**What would make it new:** it must produce a non-rank invariant — for example, a height-spectrum, a Diophantine exponent, or a transcendence-degree lower-bound profile.

---

## 5. Algebraic recurrence obstruction for the reciprocal seam sequence

The reciprocal seam moments

[
T_k=(-1)^kS_k
]

are the global RH coordinate when we ask Stieltjes positivity. But for HT, do not ask whether (T_k) is positive. Ask whether the sequence ({T_k}) satisfies any finite algebraic recurrence of bounded complexity.

Candidate detector:

[
\mathcal R_{r,d,H}(T)
=====================

\min
\left|
P(T_k,T_{k+1},\ldots,T_{k+r})
\right|
]

over all nonzero integer polynomials (P) of degree (\le d), height (\le H), and over a range of (k).

A low-complexity divisor like arithmetic progression zeros should generate structured reciprocal moments. Zeta’s reciprocal moments may resist finite algebraic recurrence.

**Why plausible:** it works on the divisor’s arithmetic sequence rather than the support geometry.

**Caution:** D-algebraic functions do not always translate into simple linear recurrences for coefficients. So this is not theorem-ready unless the target class is carefully defined: D-finite, algebraic generating functions, finite exponential sums, finite-order nonlinear recurrences, etc.

---

## 6. Divisor-arithmetic entropy / height-spectrum detector

This is a more statistical but still arithmetic candidate.

Given a value set (X_N), define its relation-height spectrum:

[
E_{N,d}(H)
==========

-\log \mathcal M_{N,d}(H).
]

Then compare growth rates:

[
E_{N,d}(H)
\quad\text{for}\quad
X_N={\gamma_n},
]

against controls:

[
\text{arithmetic progression zeros},
]

[
\text{random matrix zeros},
]

[
\text{same-density random zeros},
]

[
\text{D-algebraic toy divisors},
]

[
\text{FE-symmetric artificial divisors}.
]

The detector is not a single relation. It is the **shape of the minimal relation spectrum**.

**Why plausible:** it could separate arithmetic-complex divisors from geometrically similar but arithmetically simpler divisors.

**What would count as progress:** finding a stable spectral profile that is invariant under geometry-preserving controls but changes under arithmetic simplification.

---

## 7. Explicit-formula arithmetic-transfer obstruction

The explicit formula links prime data and zero data. The B/C-axis uses this as a positivity-transfer problem: integer/prime divisor (\to) zero-divisor Stieltjes wall. The A-axis version would ask:

> If there were an algebraic relation among zero-side values, what relation would it force among prime-log values?

A detector could be built as a map:

[
\mathcal E:
\text{relations among } {S_k}
\longrightarrow
\text{relations among } {\log p}.
]

Then a candidate theorem would say:

[
P(S_1,\ldots,S_N)=0
\quad
\Longrightarrow
\quad
Q(\log p_1,\ldots,\log p_M)=0
]

for some nonzero (Q), at controlled degree/height.

Under Schanuel-for-prime-logs, this would forbid the (S_k)-relation.

**Why plausible:** it makes precise the phrase “(\xi)'s HT is divisor-encoded and tied to ({\log p}) through the explicit formula.”

**Caution:** your notes correctly say this algebraic-independence bridge is conjectural, not proved.

---

## 8. Period-lattice leakage detector

The fused seam formula shows that (S_k) mixes at least three families:

[
\text{π-periods } \zeta(2k),
]

[
\text{Dirichlet beta / Catalan-family values } \beta(2k),
]

[
\text{prime-side derivatives }(\zeta'/\zeta)^{(2k-1)}(1/2).
]

A possible detector is:

[
\text{Does the field generated by the seam values require infinitely many new period directions?}
]

For example, define

[
F_N
===

\mathbb Q\big(
\pi,,
\beta(2),\ldots,\beta(2N),,
S_1,\ldots,S_N
\big)
]

and test whether the prime-side derivative contributions can be contained in a finitely generated period-like field.

**Why plausible:** this is genuinely value arithmetic and uses the seam identity as data, not geometry.

**Risk:** very little is known unconditionally about algebraic independence of Catalan-type constants and beta values. This route may be as hard as the original Schanuel apex.

---

## 9. Finite-generator divisor model exclusion

This is the “sin (\pi s)” contrast made into a test.

A D-algebraic / D-finite / finite-generator toy class often has a divisor produced by low-complexity rules:

[
\text{arithmetic progression},
]

[
\text{finite union of lattices},
]

[
\text{zeros of exponential polynomials},
]

[
\text{recurrence-generated sequences},
]

[
\text{algebraic deformations of a finite template}.
]

The candidate detector asks whether ({\gamma_n}) can be compressed into any such finite arithmetic generator.

One could define a compression complexity:

[
C_N({\gamma_n})
===============

\min{\text{description complexity of a finite arithmetic model fitting first }N\text{ zeros}}.
]

**Why plausible:** it directly contrasts (\xi) with order-one D-algebraic examples like sine.

**Limitation:** this is a model-class detector, not a theorem about all D-algebraic functions unless the class is greatly expanded.

---

## 10. Non-rank value matroid detector

Since rank of shift/derivative matrices is the known recurring collapse, the next candidate should be a **matroid of algebraic dependencies**, not just linear rank.

For a family of values (V={v_i}), define a matroid where a subset is dependent if there exists an algebraic relation of bounded degree/height. Then study how this matroid grows as more values are added.

Candidate invariant:

[
\mathsf{AMat}_{d,H}(V_N)
========================

\text{algebraic-dependence matroid of }V_N
\text{ up to degree }d\text{ and height }H.
]

A new detector would show that the zeta divisor has a growth pattern unlike any D-algebraic control, and not reducible to the rank of a derivative/shift matrix.

**Why plausible:** it directly addresses the failure mode named in the corpus: everything collapses to rank. This replaces rank with bounded algebraic dependence structure.

**Computational version:** exact shell search plus relation-certificate logging.

---

# My ranking of candidates

I would rank the candidates like this.

## Most direct A-axis candidate

[
\boxed{
\textbf{Prime-log Schanuel shell-profile detector.}
}
]

It targets the conjectural apex head-on. It is also maximally hard.

## Most zeta-native candidate

[
\boxed{
\textbf{Seam-value algebraic independence detector for } {S_k}.
}
]

It uses the object’s own reciprocal seam values, and the fused formula ties them to archimedean and prime-side value families.

## Most computationally practical candidate

[
\boxed{
\textbf{Exact shell-minimum spectra for }{\log p},{\gamma_n},{S_k}.
}
]

This is not proof, but it can quickly separate serious candidates from random-residual illusions.

## Most conceptually new candidate

[
\boxed{
\textbf{Algebraic-dependence matroid / height-spectrum detector.}
}
]

This is the best attempt to escape plain shift/derivative rank.

## Most theorem-shaped candidate

[
\boxed{
\textbf{Explicit-formula arithmetic-transfer obstruction.}
}
]

A theorem of the form

[
\text{zero-side algebraic relation}
\Rightarrow
\text{prime-log algebraic relation}
]

would be a genuine bridge into Conjecture A. It is likely very hard.

---

# What would count as a real win?

A candidate detector becomes serious only if it passes these tests.

1. **Geometry quotient:** It does not change merely because zeros move on/off the seam; it detects arithmetic relations, not location.

2. **Sine contrast:** It distinguishes (\xi)-type divisor arithmetic from (\sin \pi s)-type arithmetic-progression divisors.

3. **Non-rank audit:** It does not reduce to shift/derivative matrix rank.

4. **Exact-shell coverage:** It uses exact or certified coefficient-shell searches, not random residual histograms.

5. **Explicit-formula compatibility:** It respects the relationship between ({\gamma_n}), ({S_k}), and ({\log p}) without pretending that the algebraic-independence bridge is already proven.

6. **Control ladder:** It separates zeta from same-density, same-pair-correlation, same-RH-geometry but arithmetic-randomized divisors.

7. **Theorem target:** It can be stated as a lower-bound / nonexistence theorem for algebraic relations, not just an empirical statistic.

---

# The sharpest speculative answer

The genuinely new detector is probably not a single observable like (\Delta), (T_k), or a contour integral.

It is likely a **Diophantine profile**:

[
\boxed{
\textbf{the height-shell spectrum of algebraic relations among the divisor-arithmetic values}
}
]

applied to one of these value families:

[
{\log p},
\qquad
{\gamma_n},
\qquad
{S_k},
\qquad
\left{(\zeta'/\zeta)^{(j)}(1/2)\right}.
]

In one compact formula, I would define the prototype detector as

[
\boxed{
\mathcal A_{X}(N,d,H)
=====================

\min_{\substack{0\ne P\in\mathbb Z[x_1,\ldots,x_N]\
\deg P\le d,\ H(P)\le H}}
\left|P(X_1,\ldots,X_N)\right|,
}
]

where (X) is one of the divisor-arithmetic value families above.

The detector is not the value of (\mathcal A_X) once. It is the asymptotic profile of

[
(N,d,H)\mapsto \mathcal A_X(N,d,H)
]

under exact shell coverage and against arithmetic controls.

That is the cleanest candidate because it lives exactly where the documents say the detector must live: not on geometry, not on holonomy, but on algebraic relations among divisor values. The current corpus says this A-axis detector has not been found, and that the known value-level separations collapse to shift/derivative rank; the shell-profile / algebraic-matroid route is the most plausible way to try to escape that collapse.
