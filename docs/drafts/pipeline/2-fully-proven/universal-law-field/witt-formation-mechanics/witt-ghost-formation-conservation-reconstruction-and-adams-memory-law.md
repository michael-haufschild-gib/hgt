# Witt ghost--formation conservation, reconstruction, and Adams memory law

- **ID:** ULF-WFM-2
- **Stage:** 2-fully-proven
- **Type:** ROUTE-INDEPENDENT FUSION THEOREM
- **Parent:** `full-frontier-intervention-generation-grammar.md`
- **Statement:** One finite mode packet generates bosonic formation, exterior cancellation,
  primitive ghost current, and Adams intervention; the first ghost packet reconstructs every
  formation shadow, exact inverse conservation holds, and Adams collisions predict the minimal
  recurrence/Hankel memory in a fourth organ.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [THREE-ORGAN FUSION]
  [JOINT RECONSTRUCTION] [EXACT CONSERVATION] [FOURTH-ORGAN PREDICTION]
  [LEAN-CERTIFIED FINITE CORE] [UMBRELLA WIRED] [NOT RH]

## 1. Setup

Let \(x=(x_1,\ldots,x_r)\in\mathbb C^r\), with \(r\ge 1\). Define

\[
 p_n(x)=\sum_{i=1}^r x_i^n\quad(n\ge1),
 \tag{WFM.1}
\]

\[
 E_x(t)=\prod_{i=1}^r(1+x_it)=\sum_{k=0}^r e_k(x)t^k,
 \qquad
 H_x(t)=\prod_{i=1}^r(1-x_it)^{-1}=\sum_{n\ge0}h_n(x)t^n.
 \tag{WFM.2}
\]

The three input organs are structurally different.

1. \(h_n\) is the unrestricted/bosonic formation or allocation response.
2. \(e_k\) is the hard-core/exterior response; its signed specialization is determinant/parity.
3. \(p_n\) is the primitive/ghost response, equivalently a trace, connected current, or
   logarithmic jet.

For an integer \(q\ge 1\), the Adams intervention is

\[
 \psi^q x=(x_1^q,\ldots,x_r^q),
 \qquad p_n(\psi^q x)=p_{qn}(x).
 \tag{WFM.3}
\]

## 2. Master fusion theorem

### Theorem 2.1 — conservation, generation, and joint reconstruction

The packet \(x\) satisfies all of the following.

1. **Exact formation/exterior conservation:**
   \[
    E_x(-t)H_x(t)=1.
    \tag{WFM.4}
   \]
   Hence \(h_0=e_0=1\) and, for every \(n\ge 1\),
   \[
    \sum_{k=0}^{\min(n,r)}(-1)^k e_k(x)h_{n-k}(x)=0.
    \tag{WFM.5}
   \]

2. **Ghost generation:**
   \[
    t{H_x'(t)\over H_x(t)}
       =\sum_{n\ge1}p_n(x)t^n.
    \tag{WFM.6}
   \]
   Coefficientwise,
   \[
    n h_n(x)=\sum_{k=1}^n p_k(x)h_{n-k}(x).
    \tag{WFM.7}
   \]
   The exterior companion obeys
   \[
    n e_n(x)=\sum_{k=1}^n(-1)^{k-1}p_k(x)e_{n-k}(x)
    \qquad(1\le n\le r).
    \tag{WFM.8}
   \]

3. **Joint reconstruction:** over characteristic zero, the finite ghost packet
   \((p_1,\ldots,p_r)\) recursively determines \((e_1,\ldots,e_r)\) by `(WFM.8)`, hence determines
   \[
    \chi_x(T)=T^r-e_1T^{r-1}+e_2T^{r-2}-\cdots+(-1)^re_r.
    \tag{WFM.9}
   \]
   Its multiset of roots is exactly \(\{x_1,\ldots,x_r\}\). It therefore determines every
   \(p_n,e_n,h_n\), every Adams response, and every polynomial response symmetric in the modes.

Thus formation, signed exterior cancellation, and primitive analytic current are not independent
coordinates.  They are generated shadows of one finite Witt response.

### Proof

Equation `(WFM.4)` is multiplication of the factors in `(WFM.2)`. Extracting the coefficient of
\(t^n\) proves `(WFM.5)`.

In the formal power-series ring,

\[
 t{H_x'\over H_x}
 =\sum_i {x_it\over1-x_it}
 =\sum_i\sum_{n\ge1}x_i^nt^n
 =\sum_{n\ge1}p_n(x)t^n,
\]

proving `(WFM.6)`. Multiplying by \(H_x\) and comparing \(t^n\)-coefficients proves
`(WFM.7)`. The same calculation with \(E_x\), or Newton's identity, gives `(WFM.8)`.

Since every integer \(1,\ldots,r\) is invertible in \(\mathbb C\), `(WFM.8)` recursively determines
each \(e_n\) from \(p_1,\ldots,p_n\). Vieta's formula gives `(WFM.9)` and its root multiset.
All remaining symmetric responses are then determined. ∎

## 3. Withheld fourth-organ prediction

The first three organs use no recurrence or Hankel-rank premise. Those are consequences of the
fusion law. Generic finite packet recurrence already existed in the corpus; the withheld
specialization here is the exact identification of its minimal order and stable rank with the
collision quotient of an Adams intervention.

Fix \(q\ge 1\), and let

\[
 Y_q=\{x_i^q:1\le i\le r\}=\{y_1,\ldots,y_s\}
 \tag{WFM.10}
\]

be the distinct \(q\)-th-power modes, and let \(m_a\ge 1\) be the multiplicity of \(y_a\). Put

\[
 g_n^{(q)}=p_{qn}(x)=\sum_{a=1}^s m_a y_a^n\qquad(n\ge0),
 \tag{WFM.11}
\]

where \(g_0^{(q)}=r\), and write

\[
 \prod_{a=1}^s(T-y_a)
 =T^s-c_1T^{s-1}+c_2T^{s-2}-\cdots+(-1)^sc_s.
 \tag{WFM.12}
\]

### Theorem 3.1 — Adams collision equals exact process-memory loss

1. The post-Adams ghost sequence has the recurrence
   \[
    g_{n+s}^{(q)}
    =c_1g_{n+s-1}^{(q)}-c_2g_{n+s-2}^{(q)}+\cdots
      +(-1)^{s+1}c_sg_n^{(q)}
    \qquad(n\ge0).
    \tag{WFM.13}
   \]
2. No monic recurrence of smaller order annihilates the whole sequence.
3. For every \(N\ge s\), the \(N\times N\) Hankel matrix
   \[
    \mathcal H_N^{(q)}=(g_{i+j}^{(q)})_{0\le i,j<N}
    \tag{WFM.14}
   \]
   has rank exactly \(s\).
4. Hence the Adams intervention loses exactly
   \[
    r-|Y_q|
    \tag{WFM.15}
   \]
   units of finite mode memory, and loses none exactly when \(x\mapsto x^q\) is injective on the
   marked mode set.
5. If the modes are distinct positive reals, every Adams intervention preserves memory rank, and
   every real Hankel matrix in `(WFM.14)` is positive semidefinite.

This is the required fourth-organ prediction: ramification/Adams action does not merely rescale
the analytic response.  Its collision quotient is exactly the minimal recurrence order and stable
Hankel rank of the resulting process.

### Proof

Each \(y_a\) is a root of `(WFM.12)`, so

\[
 y_a^{n+s}=c_1y_a^{n+s-1}-c_2y_a^{n+s-2}+\cdots+(-1)^{s+1}c_sy_a^n.
\]

Multiply by \(m_a\), sum over \(a\), and use `(WFM.11)` to obtain `(WFM.13)`.

If a monic polynomial \(Q\) of degree \(d<s\) supplied a recurrence, then

\[
 \sum_{a=1}^s m_aQ(y_a)y_a^n=0\qquad(n\ge0).
\]

Taking \(n=0,\ldots,s-1\), the square Vandermonde matrix on the distinct \(y_a\) is invertible.
Therefore \(m_aQ(y_a)=0\) for every \(a\), hence \(Q(y_a)=0\) for all \(s\) distinct points,
contradicting \(\deg Q<s\). This proves minimality.

For \(N\ge s\), let \(V=(y_a^i)_{0\le i<N,1\le a\le s}\) and
\(D=\operatorname{diag}(m_1,\ldots,m_s)\). Then

\[
 \mathcal H_N^{(q)}=VDV^{\mathsf T}.
 \tag{WFM.16}
\]

The Vandermonde columns are independent, so \(V\) has a left inverse \(L\). Consequently
\(L\mathcal H_N^{(q)}L^{\mathsf T}=D\), proving rank at least \(s\); `(WFM.16)` proves rank at
most \(s\). This gives item 3 and `(WFM.15)`. Positive real powers are injective on distinct
positive reals. In that chamber, `(WFM.16)` gives
\(u^{\mathsf T}\mathcal H_N^{(q)}u=\sum_a m_a|(V^{\mathsf T}u)_a|^2\ge0\), proving item 5. ∎

## 4. Exact three-to-four organ ledger

| role in user-mandated experiment | generated response |
|---|---|
| organ 1: allocation / formation | \(h_n\), coefficients of \(H_x\) |
| organ 2: exclusion / signed determinant | \(e_n\), coefficients of \(E_x\) and \(E_x(-t)=H_x^{-1}\) |
| organ 3: primitive analytic current / intervention | \(p_n\), logarithmic derivative, Adams subsequence \(p_{qn}\) |
| joint conservation | \(E_x(-t)H_x(t)=1\) |
| joint reconstruction | \(p_1,\ldots,p_r\Rightarrow e_1,\ldots,e_r\Rightarrow x\Rightarrow H,E,P\) |
| withheld organ 4: recurrence / Hankel memory | minimal order and stable rank \(=|\{x_i^q\}|\) |

## 5. Hostile audit and sharp boundary

1. **Not a bundle.** The load-bearing datum is \(H_x\). Inversion gives \(E_x(-t)\), logarithmic
   differentiation gives \(P_x\), and Adams acts on the same modes. Removing these compatibility
   laws destroys reconstruction and the memory prediction.
2. **Characteristic zero is load-bearing for ghost reconstruction.** Over rings with torsion the
   ghost map may fail to be injective; this is a genuine completion/integrality boundary, not a
   technicality.
3. **Finite rank is load-bearing.** Infinite ghost packets need topology, convergence, and a
   moment/realization theorem.  Finite identities do not provide a compact cofinal carrier.
4. **Positivity is a realization chamber, not the source law.** Complex modes retain determinant
   phase but their transpose-Hankel matrices need not be positive.  Positive real modes give the
   PSD clause but erase phase.
5. **Adams collision is not RH selection.** Positive Euler modes have no power collisions, so raw
   Adams action preserves memory.  A critical-line conclusion would require a completed
   reflection-marked source law, not this finite algebra.
6. **HT is not infinite Fock rank.** The theorem predicts finite linear memory.  Infinite or
   hypertranscendental response requires a separate cofinal/prolongation theorem.

## 6. Field consequence

The theorem establishes the middle of the extracted grammar:

\[
 \textsf{form}\longleftrightarrow\textsf{ghost}
 \longleftrightarrow\textsf{dualize},
 \qquad
 \textsf{Adams intervention}\longrightarrow\textsf{memory prediction}.
\]

The next nonlocal problem is exact and no longer vocabulary-level: determine whether the literal
Euler--Gamma source admits a completed, reflection-marked Witt formation for which these operations
remain jointly admitted and coefficient-faithful.  Only after that theorem may its conservation law
be tested against the retained RH horizontal class.

## 7. Parent mathematics

Newton identities, symmetric/exterior power generating functions, special \(\lambda\)-rings, big Witt
ghost coordinates, finite Prony/Hankel realization, and Vandermonde rank are classical.  Relevant
primary parents include work on Adams operations and power structures and on Adams operations in
representation categories.  The point here is the field mechanism: one generated response law
meets the mandated three-organ fusion, conservation/reconstruction, and fourth-organ prediction.
No isolated ingredient is presented as a new theorem of classical algebra.

## 8. Lean certification

The unconditional finite core is formalized in
`GaloisForLFunctions.HTGeometry.WittFormationMechanics` and wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField`:

- inverse formation conservation;
- ghost/Newton recursion and first-\(r\)-ghost multiset reconstruction;
- Adams ghost subsampling and exact collision aggregation;
- recurrence generated by the post-Adams characteristic polynomial;
- exact saturated Hankel rank and minimal recurrence order;
- collision-free positive-real chamber.

No analytic infinite product, RH endpoint, or conjectural completed source is a Lean target.

## Gates

- [x] one source formation generates three structurally different organs
- [x] exact conservation identity proved
- [x] finite joint reconstruction proved
- [x] fourth-organ recurrence/Hankel theorem predicted and proved
- [x] hostile finite/cofinal, positivity/phase, and Adams/RH boundaries recorded
- [x] Lean formalization and umbrella wiring
- [ ] completed source realization
- [ ] RH consequence, forbidden before completed realization

## Log

- 2026-08-11 — theorem frozen after martingale, commutator, cocycle, bare Hopf, and arbitrary
  endogeneity candidates were rejected as regressions or vacuous containers.
- 2026-08-11 — Lean module elaborated and compiled; generic packet recurrence collision was
  acknowledged explicitly, while Adams collision aggregation/minimal memory remains the fused
  specialization certified here.
