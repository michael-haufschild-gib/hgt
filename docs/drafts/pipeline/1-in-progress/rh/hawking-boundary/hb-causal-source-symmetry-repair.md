# HB: causal repair of the source symmetry

- **ID:** HB-CAUSAL-SOURCE-SYMMETRY-REPAIR
- **Stage:** 1-in-progress
- **Parent:** [Source-contact rigidity](../../hb-source-contact-rigidity.md)
- **Status:** Candidate deferred. The paper commutator omitted a second-time-derivative term, corrected below on 12 September 2026. No new closed Lean theorem, extinction, or RH proof. Do not resume this invented symmetry as a substitute for deriving the actual complete-action cancellation.

Proof chain: literal theta cusp → Xi occurrence → retained spin two → physical causal radial/left-QNM action → extinction at the original common Hawking clock → RH.

The hard question is whether the original nonlinear equations cancel the complete oriented action. Further cusp estimates are deferred while testing this mechanism directly. The 779-line linear-current scratch `/tmp/hb-tested-linear-current.lean` passed `lake env lean` at default limits, but is not published or audited as a new leaf. It does not prove extinction.

## 1. Interior repair is not a boundary-domain identity

Use the original variables of the parent calculation:

```
u=-tanh x, V=u²-1, b=u²/(1-u),
K=(7lambda-2-2Delta)/8,
M=-partial_x²-2partial_x partial_v+V Delta,
T=K[b(partial_x+partial_v)-b'/2].
```

The formal complex-bilinear transpose in `dx dv dX dy/y²` is
`T^dagger=K[-b(partial_x+partial_v)-3b'/2]`. The parent product-rule calculation therefore gives

```
M T+T^dagger M = E,
E=K[b'''/2-2b' partial_v²-(b V'+2b' V)Delta].          (1)
```

The earlier version of (1) incorrectly omitted `-2Kb' partial_v²`, arising from `[-2 partial_x partial_v,b partial_v]`. E is a second-order operator, not a multiplier. On a time mode exp(wv), its extra term is `-2Kb'w²`. The angular operator has not been replaced by a scalar eigenvalue. The AdS coefficient trace remains `-3K`, since b'(0)=0. Every later use of E means this corrected operator; the Green-admission claims remain conditional.

**Conjecture R1:** subtracting the actual retarded response to E produces a physical symmetry. The interior calculation alone does not prove it. If the original Green operator is admitted on the required source, define

```
T_r=T-G_r E,  T_a=T-G_a E.
```

Right inversion gives `M T_r=-T^dagger M` and the advanced counterpart, but

```
T_r-T_a=-(G_r-G_a)E.                                  (2)
```

Thus the two causal prescriptions differ by the radiative response to the commutator source. This is not a vanishing theorem.

For a homogeneous physical mode psi, (1) gives `E psi=M(T psi)`. Consequently

```
T_r psi=(1-G_r M)T psi.                               (3)
```

The right side is the homogeneous field carrying the boundary/initial data of `T psi`. Replacing `G_r M` by the identity on a QNM silently removes those data. The existing source inverse theorems do not license that replacement on arbitrary QNM fields. Equations (2)–(3) are interface calculations conditional on Green admission, not new source theorems.

## 2. Exact physical fundamental boundary test

Let rho be the original Xi occurrence. The verified corpus definitions give

```
lambda=rho(rho-1), mu=rho(rho-2)/4,
w=-1-rho/2 or w=-2+rho/2,
z=1-u², phi_w=u z^(w/2),
k=(7lambda-2-2mu)/8=(13rho²-12rho-4)/16.
```

Both actual horizon and normalizable fundamental radial modes equal phi_w. In static coordinates `partial_x|v+partial_v=partial_x|t`, so the radial action of T on this angular eigenspace is `k[b partial_x-b'/2]`. Differentiating the displayed elementary mode gives

```
phi_w'=[(w+1)u²-1]z^(w/2),
T phi_w / phi_w = k u²[(2w+1)u+1]/[2(1-u)].             (4)
```

All quotients here are on the open physical radial interval, where phi_w is nonzero. In particular,

```
lim_(u→1-) (1-u) T phi_w/phi_w = k(w+1).               (5)
```

This coefficient is nonzero. The corpus proves `Im rho != 0`, hence `w+1 != 0`. If `13rho²-12rho-4=0`, its imaginary part forces `Re rho=6/13`; its real part then equals `-88/13-13(Im rho)²`, a contradiction. At AdS, the ratio in (4) is O(u²), so T phi_w vanishes as O(u³).

**Conjecture R2:** the horizon pole alone excludes the repair. This overstates the conclusion, because the physical reader is a finite part. The pole excludes a naive preservation of the original regular horizon factor. It does not exclude a correction with the full prescribed horizon subtraction.

There is an exact positive survivor. Pair the mode and repaired mode at opposite time frequencies. For the outward Green-current convention
`j_x=-phi_w (T phi_w)'+phi_w' T phi_w`, formula (4) gives

```
j_x=k z^(w-1) H_w(z),
H_w(z)=u³(1+u)²[1+(3w+1)u-(2w+1)u²].                  (6)
```

The function H_w is analytic near z=0. Expanding its explicit powers of `u=sqrt(1-z)` yields

```
H_w(z)=4(w+1)-6(w+1)z-(5w+1)z²/4+O(z³).
```

Thus the three divergent flux terms are exactly

```
k[4(w+1)z^(w-1)-6(w+1)z^w-(5w+1)z^(w+1)/4].          (7)
```

After their subtraction, the remainder is `O(z^(Re w+2))` in norm and tends to zero, since the original fundamental frequencies satisfy `Re w>-2`. The AdS flux tends to zero as well. This proves a paper finite-part cancellation for the same-mode commutator pairing, without changing w. It still requires identification with the repository's precise physical finite-part prescription before becoming a physical theorem. It has not been Lean-checked.

## 3. The off-diagonal source work that survives

**Conjecture R3:** the same-mode cancellation proves nonlinear radiative extinction. It does not: the action contains pairings of two different quadratic sources, not only the homogeneous mode with itself.

The precise finite-domain identity can be derived before any limit. Write `F=M f`, `G=M g`, and let `B_M(f,h)` denote the boundary integral of

```
j_x=[-f(h_x+h_v)+(f_x+f_v)h]/y²,
j_v=(-f h_x+f_x h)/y²,
j_X=V(f h_X-f_X h),  j_y=V(f h_y-f_y h).
```

For `C=b(partial_x+partial_v)-b'/2`, let `B_T(f,h)` denote the boundary integral of

```
t_x=t_v=b f K h/y²,
t_X=[(C f)h_X-h(C f)_X]/4,
t_y=[(C f)h_y-h(C f)_y]/4.
```

All faces have their outward signs. Product differentiation gives
`B_M(f,h)=<f,Mh>-<Mf,h>` and
`B_T(f,h)=<Tf,h>-<f,T^dagger h>` in the original volume measure. Substitution in (1) proves

```
<f,E g>=<F,Tg>+<Tf,G>+B_M(f,Tg)-B_T(f,G).              (8)
```

In particular, with the actual left mode psi and a retarded response g to S, the required interface is

```
<psi,E G_r S>=<T psi,S>
              +B_M(psi,T G_r S)-B_T(psi,S).            (9)
```

Equation (9) retains source work. Neither the zero same-mode finite part nor an interior inverse removes it. Horizon, cusp, temporal and characteristic/source-contact faces must be obtained by restricting this finite balance and then taking the original admitted limits; internal interfaces must not be counted twice.

## 4. Nonlinear extension is the next actual obstruction

The proposed generator is not a derivation of products. With `kappa=(7lambda-2)/8`, the exact angular product rule is

```
K(fg)-f Kg-g Kf=-kappa fg-Gamma(f,g)/2.                 (10)
```

For the literal eigenfield f, this is the source of the retained gradient term in `K(f²/2)`. Dropping it would erase the original contact. Extending (1) to the Einstein quadratic map B therefore needs its actual defect

```
O_2(p,m)=T B(p,m)-B(Tp,m)-B(p,Tm),
```

with the tensorial extension of T first specified and checked. This is an unproved candidate, not an asserted Einstein identity. A causal correction obtained by applying `G_r` to O_2 again differs from its advanced counterpart by `(G_r-G_a)O_2`; that difference must be evaluated in the actual left-QNM action.

The defect can already be evaluated on the actual scalar half-square, before pretending it is the full tensor B. For arbitrary smooth scalar fields f,g, put `D=partial_x+partial_v`. Expanding (10) gives the exact interior formula

```
T(fg)-(Tf)g-fTg
 = kappa b' fg/2+b' Gamma(f,g)/4
   -b[(Df)Delta g+(Delta f)Dg
       +2Gamma(Df,g)+2Gamma(f,Dg)]/4.                  (11)
```

For the unswitched literal theta leg `p=a_s theta`, with
`a_s=A exp(sv)(1+u)^s`, one has `D a_s=s u a_s` and
`Delta theta=lambda theta`. Retain `Q=theta²/2` and `J=KQ`.
Substitution in (11), using the original identity
`Gamma(theta,theta)=(3lambda-2)theta²/4-4J`, yields

```
T(p²/2)-p Tp
 =a_s²[(5lambda-2)(b'-2s u b)Q/8
                 +(-b'/2+2s u b)J].                 (12)
```

Thus even this actual quadratic source has two retained angular terms; the proposed symmetry does not pass through its assembly by a Leibniz argument. The original switched source has chi rather than an arbitrarily chosen square-root onset. Its additional exact commutator is

```
T(chi F)-chi T(F)=b chi' K F.                          (13)
```

Here chi is precisely `Real.smoothTransition(v)`, so the source-contact support is unchanged. Equations (11)–(13) follow by differentiation and do not assume any source term vanishes. They are paper identities, not newly verified Lean declarations. Matching their Q, J and chi' terms to the actual solved tensor corrections, rather than deleting them or defining a new correction, is the remaining test of this candidate.

This proposed O_2 investigation is deferred by the user's explicit direction to attack the actual RH source-extinction problem. No tensorial extension or nonlinear symmetry has been established. No channel orthogonality, source-dependent clock correction, Green-domain equality, or vanishing boundary is a permitted premise. Merely introducing O_2 or an inverse is not progress on the physical projection.

The final sufficient physical interface remains `Cphys=K=-Sigma|D|²`, `Sigma>0`, together with a source-derived `Re Cphys>=0`, or a strict bound `-Re Cphys<=epsilon Sigma|D|²` with `epsilon<1`. Nothing above proves that orientation. The full goal remains open.

## Search and method audit

Deep and hybrid/method corpus searches for source/adjoint repair and horizon poles inspected candidate lemmas, source arguments and ingredient sets. The two repair requests returned no retrieval errors with 57,228 inventoried files; compiler metadata remained largely pending and semantic coverage unmeasured. The deep ingredient group concerned abstract adjoint commutators, not physical Green admission. The horizon request inventoried 57,229 files and recovered the actual fundamental modes, horizon finite parts and original source-action residues. No retrieved theorem evaluated (9) for the complete nonlinear source. Earlier finite-clock deep search was partial with semantic timeouts; its clock-map ingredient group did not prove invariance.

Broad arXiv searches used transmutation, intertwining, rigidity, anomaly, recurrence and transgression. Most results were irrelevant; some date-filtered searches returned older papers. Dates below are the papers' actual dates.

- [Frassek–de Gier–Li–Verstraete, Intertwining Markov Processes via Matrix Product Operators](https://arxiv.org/html/2603.09928v2), version 13 May 2026: equations (5)–(6) give a bulk telescoping relation and two independent boundary equations. The boundary equations complete the global intertwiner. Transfer tested: repair a bulk symmetry with causal boundary terms. This motivates (8)–(9); their boundary equations are not HB source laws, and their map changes the boundary process. The paper also retains nonzero steady currents.
- [Elber–Lheem, Intertwining Operators for Siegel Parabolics over Finite Fields](https://arxiv.org/html/2608.01485v1), 2 August 2026: Section 2.4 constructs an actual Weyl intertwiner by a finite unipotent sum; the character spaces and their boundary-free finite-group setting are explicit. No identification with HB's causal domain or source current was found.
- [Pais–Salgado-Rebolledo–Vera, Hamiltonian structure of transgression forms](https://arxiv.org/pdf/2309.16760), December 2023 version: equations (3.17)–(3.19) and (4.1)–(4.3) retain boundary variations and surface charges even when bulk constraints vanish. This defeats the inference that restoring action symmetry sets every surface charge to zero; no transgression representation of the full HB Einstein action was derived.

No paper is used as an unproved Lean premise. No numerical calculation or resource-limit override was run for this attack.
