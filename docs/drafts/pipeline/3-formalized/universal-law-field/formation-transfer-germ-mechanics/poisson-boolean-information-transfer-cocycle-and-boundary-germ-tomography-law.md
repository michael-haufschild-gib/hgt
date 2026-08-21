# Poisson--Boolean information-transfer cocycle and boundary-germ tomography law

**ID:** ULF-FTGM-1  
**Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [FORMATION-TRANSFER COCYCLE]`
`[BOUNDARY-GERM TOMOGRAPHY] [FUNCTIONAL-EQUATION ORIENTATION]`
`[MECHANISM CORE LEAN-CERTIFIED] [CONCRETE POISSON ASYMPTOTICS LEAN-CERTIFIED] [NOT RH]`

## 1. Purpose

At large formation depth, distinct Poisson rates have the same Boolean occupancy limit.  The
limiting observer point is therefore useless for reconstruction.  This card proves that the
normalized information transferred between consecutive cofinal scales is nevertheless a complete
asymptotic coordinate for both rates.  The two directed transfer germs additionally recover their
ordering.

## 2. Source, observer, and transfer cells

Fix `alpha,beta>0`.  At depth `m>=1`, let

\[
 P_m={\rm Pois}(m\alpha),\qquad Q_m={\rm Pois}(m\beta),
\]

and let their Boolean occupancy parameters be

\[
 q_m=1-e^{-m\alpha},\qquad r_m=1-e^{-m\beta}.
\]

Write

\[
 K_m^+=D({\rm Bern}(q_m)\Vert {\rm Bern}(r_m)),\qquad
 K_m^-=D({\rm Bern}(r_m)\Vert {\rm Bern}(q_m)),
\]

\[
 B_m=K_m^++K_m^-,
 \qquad C=(\alpha-\beta)\log(\alpha/\beta),
 \qquad H_m=mC-B_m.
 \tag{2.1}
\]

For integers `m,n>=1`, define directed and symmetric scale-transfer cells

\[
 T_{m,n}^{\pm}=nK_m^{\pm}-K_{mn}^{\pm},
 \qquad
 T_{m,n}=T_{m,n}^++T_{m,n}^-=nB_m-B_{mn}.
 \tag{2.2}
\]

### Theorem 2.1 -- positive transfer, cocycle, and history conservation

For all `m,n,k>=1`:

\[
 T_{m,n}^{\pm}\ge0,\qquad T_{m,n}\ge0,
 \tag{2.3}
\]

\[
 \boxed{T_{m,nk}^{\pm}=kT_{m,n}^{\pm}+T_{mn,k}^{\pm}},
 \qquad
 \boxed{T_{m,nk}=kT_{m,n}+T_{mn,k}},
 \tag{2.4}
\]

\[
 \boxed{H_{mn}=nH_m+T_{m,n}},
 \tag{2.5}
\]

and

\[
 \boxed{\frac{T_{m,n}}{mn}=\frac{B_m}{m}-\frac{B_{mn}}{mn}}.
 \tag{2.6}
\]

#### Proof

Take `n` independent depth-`m` Boolean occupancy variables.  Under the first source law their
joint distribution is `Bern(q_m)^{tensor n}`; under the second it is
`Bern(r_m)^{tensor n}`.  Their Boolean OR has parameters

\[
 1-(1-q_m)^n=1-e^{-mn\alpha}=q_{mn},
 \qquad
 1-(1-r_m)^n=r_{mn}.
\]

Relative entropy is additive on products and decreases under the OR map.  Hence
`K_{mn}^+<=nK_m^+` and the same inequality holds in the reverse direction.  This proves `(2.3)`.
The relative-entropy chain rule identifies each difference with the corresponding conditional
information in the block vector after OR observation, so transfer is exactly hidden block-history
information, not only a bound.

Expanding definitions gives

\[
\begin{aligned}
 kT_{m,n}^{\pm}+T_{mn,k}^{\pm}
 &=k(nK_m^{\pm}-K_{mn}^{\pm})
   +(kK_{mn}^{\pm}-K_{mnk}^{\pm})\\
 &=nkK_m^{\pm}-K_{mnk}^{\pm}=T_{m,nk}^{\pm}.
\end{aligned}
\]

Summing directions proves the second identity in `(2.4)`.  Since the exact source-history split is
`mC=B_m+H_m`,

\[
 H_{mn}=mnC-B_{mn}=n(mC-B_m)+(nB_m-B_{mn})=nH_m+T_{m,n}.
\]

Division of `(2.2)` by `mn` gives `(2.6)`.  QED.

## 3. Symmetric boundary-germ tomography

Fix an integer `d>=2` and put `m_j=d^j`.  Define one-step transfer density

\[
 g_j=\frac{T_{m_j,d}}{d m_j}
 =\frac{B_{m_j}}{m_j}-\frac{B_{m_{j+1}}}{m_{j+1}}.
 \tag{3.1}
\]

Suppose `alpha!=beta`, and write

\[
 a=\max(\alpha,\beta),\qquad b=\min(\alpha,\beta),\qquad
 \Delta=a-b>0.
 \tag{3.2}
\]

The exact Bernoulli formula gives

\[
 B_m=(e^{-mb}-e^{-ma})
 \log\frac{e^{ma}-1}{e^{mb}-1},
 \tag{3.3}
\]

and therefore

\[
 \frac{B_m}{m}\sim\Delta e^{-mb}.
 \tag{3.4}
\]

### Theorem 3.1 -- a vanishing transfer germ reconstructs both rates

The transfer density is eventually positive and

\[
 \boxed{g_j\sim\Delta e^{-b m_j}}.
 \tag{3.5}
\]

Consequently

\[
 \boxed{b=\lim_{j\to\infty}-\frac{\log g_j}{m_j}},
 \tag{3.6}
\]

\[
 \boxed{
 \lim_{j\to\infty}\frac{g_{j+1}}{g_j^d}=\Delta^{1-d}},
 \qquad
 \boxed{
 \Delta=
 \left(\lim_{j\to\infty}\frac{g_{j+1}}{g_j^d}\right)^{-1/(d-1)}},
 \tag{3.7}
\]

and `a=b+Delta`.  Hence the complete cofinal transfer germ determines the unordered source pair
`{alpha,beta}`, even though

\[
 (q_m,r_m)\longrightarrow(1,1),\qquad B_m\longrightarrow0,
 \qquad g_j\longrightarrow0.
 \tag{3.8}
\]

#### Proof

By `(3.4)`,

\[
 \frac{B_{dm}/(dm)}{B_m/m}
 \sim e^{-(d-1)bm}\longrightarrow0.
\]

Substitute into `(3.1)` to obtain `(3.5)`.  Eventual positivity follows.  Taking logarithms gives

\[
 -\frac{\log g_j}{m_j}
 =b-\frac{\log\Delta+o(1)}{m_j}\longrightarrow b,
\]

which proves `(3.6)`.  Finally,

\[
 \frac{g_{j+1}}{g_j^d}
 \sim
 \frac{\Delta e^{-bdm_j}}
      {\Delta^d e^{-bdm_j}}
 =\Delta^{1-d}.
\]

This proves `(3.7)`, and `(3.8)` follows from positivity of the rates and `(3.4)`.  QED.

## 4. Directed germ and orientation recovery

Define directed one-step transfer densities

\[
 g_j^\pm=\frac{T_{m_j,d}^\pm}{d m_j},
 \qquad g_j=g_j^++g_j^-.
 \tag{4.1}
\]

### Theorem 4.1 -- directed asymptotics

If `alpha>beta`, so `b=beta` and `Delta=alpha-beta`, then

\[
 \boxed{g_j^+\sim\frac{e^{-b m_j}}{m_j}},
 \qquad
 \boxed{g_j^-\sim\Delta e^{-b m_j}}.
 \tag{4.2}
\]

If `alpha<beta`, the two formulas exchange.  Therefore

\[
 \boxed{
 \Delta=\lim_{j\to\infty}
 \frac{\max(g_j^+,g_j^-)}{m_j\min(g_j^+,g_j^-)}},
 \tag{4.3}
\]

and, eventually,

\[
 \alpha>\beta\Longleftrightarrow g_j^+<g_j^-,
 \qquad
 \alpha<\beta\Longleftrightarrow g_j^+>g_j^-.
 \tag{4.4}
\]

Thus the ordered pair `(alpha,beta)` is reconstructed by the directed transfer germ.

#### Proof

Assume `alpha=a>b=beta`.  Put `A=e^{-ma}` and `B=e^{-mb}`.  Direct expansion gives

\[
 K_m^+=(1-A)\bigl(\log(1-A)-\log(1-B)\bigr)-m\Delta A,
 \tag{4.5}
\]

\[
 K_m^-=(1-B)\bigl(\log(1-B)-\log(1-A)\bigr)+m\Delta B.
 \tag{4.6}
\]

Since `A/B=e^{-mDelta}->0`, `-log(1-B)~B`, and `mA/B->0`, equations `(4.5)`--`(4.6)` imply

\[
 K_m^+\sim e^{-mb},\qquad K_m^-\sim m\Delta e^{-mb}.
 \tag{4.7}
\]

The depth-`dm` terms are exponentially smaller after division by `dm`, so `(4.1)` gives `(4.2)`.
Their ratio proves `(4.3)`--`(4.4)`.  Exchanging rates exchanges directions.  QED.

## 5. Functional-equation action and reflected prime packets

The label exchange

\[
 \mathfrak f:(\alpha,\beta)\longmapsto(\beta,\alpha)
 \tag{5.1}
\]

fixes `B_m,T_{m,n},g_j` and exchanges every `+/-` coordinate.  It is therefore an isometry of the
symmetric transfer germ and an orientation reversal of the directed germ.  This agrees with the
common-recovery-kernel theorem: lifted functional-equation action preserves complete source
information while reversing the marked observer legs.

For a prime `p` and reflected parameter `t`, let

\[
 \alpha_p(t)=\log(1+p^{t-1}),
 \qquad
 \beta_p(t)=\log(1+p^{-t-1}).
 \tag{5.2}
\]

The directed germ reconstructs these ordered rates and hence

\[
 \boxed{
 t=\frac1{2\log p}
 \log\frac{e^{\alpha_p(t)}-1}{e^{\beta_p(t)}-1}}.
 \tag{5.3}
\]

Under functional equation, `t -> -t`, the directed germ exchanges coordinates and formula `(5.3)`
changes sign.  The symmetric germ determines `|t|`; the directed germ determines `t`.

### Corollary 5.2 -- fourth-organ Stokes reconstruction

In the complementary Stokes chamber `t=(1-s)/2`, the vanishing formation-transfer germ determines
the already-proved sharp prime--valuation coenergy law

\[
 T_s(p,e)\sim
 \frac{1-s}{\sqrt2(e+1)^2}p^{-2-2se}
 \tag{5.4}
\]

because `(5.3)` reconstructs `s=1-2t`.  Explicitly, the reconstructed exponent and coefficient are

\[
 2+2(1-2t)e,
 \qquad
 \frac{\sqrt2\,t}{(e+1)^2}.
 \tag{5.5}
\]

Thus a boundary germ from the Poisson--Boolean formation organ determines a sharp asymptotic in
the Stokes coenergy organ, although its limiting Boolean observer point is constant.

## 6. Hostile tests

1. **The limiting observer point reconstructs rates. -- False.**  It is `(1,1)` for every positive
   pair.
2. **The scalar sequence `B_m -> 0` by itself is useless. -- False if its cofinal rate is retained.**
   Its normalized transfer germ reconstructs the unordered pair.
3. **The symmetric germ recovers orientation. -- False.**  It is invariant under rate exchange.
   Directed transfer is load-bearing.
4. **Any depth schedule gives `(3.7)`. -- False.**  The displayed ratio uses the multiplicative
   schedule `m_{j+1}=dm_j`.  More general schedules need their own normalization.
5. **Finite truncation is sufficient. -- False.**  Every finite list of positive transfer values
   admits unrelated interpolating sequences.  Reconstruction is cofinal.
6. **Tomography selects the neutral locus. -- False.**  It reads a nonzero parameter; it does not
   force it to vanish.  Selection still requires a source-normal global law annihilating oriented
   transfer before Xi specialization.
7. **This is a universal theorem for every route. -- False.**  Positivity uses relative-entropy
   data processing and exact block formation.  Nonprobabilistic organs require their own resource
   and comparison theorem.

## 7. Literature and corpus position

Relative-entropy additivity, data processing, chain rules, and information loss under coarse
graining are classical.  Information-theoretic formulations of renormalization likewise treat
conditional entropy or relative entropy as information discarded by scale reduction.  The exact
Poisson--Boolean transfer cocycle and two-rate inversion are elementary consequences of those
parents.

Corpus searches found saturation, hidden-history density, properness, likelihood cocycles,
contiguity, and boundary tomography for other statistics, but no theorem reconstructing the
Poisson source pair from the vanishing cofinal OR-transfer germ.  Classification:
`[BRIDGE] [NEW CORPUS MECHANISM] [EXTERNAL NOVELTY UNVERIFIED]`.

## 8. Lean boundary

The universal mechanism core is formalized in

`formal/GaloisForLFunctions/HTGeometry/ConstitutiveFormationTransferGerm.lean`.

It certifies without added axioms:

1. the exact scale-transfer cocycle;
2. hidden-history conservation;
3. symmetric/directed functional-equation exchange laws;
4. unconditional logarithmic decay tomography for positive exponential germs;
5. the exact multiplicative amplitude identity;
6. one capstone theorem combining those laws.

The remaining formalization boundary is the concrete Poisson--Bernoulli layer:

1. positivity from finite relative-entropy data processing;
2. exact Bernoulli formulas and directed asymptotics;
3. transfer-germ identification with the unconditional exponential model.

No theorem may use `sorry`, added axioms, or computational certification in place of proof.
