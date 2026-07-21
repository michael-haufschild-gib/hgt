# Suzuki exterior pole tomography and the exact Neumann boundary law

- **ID:** `suzuki-exterior-pole-tomography-neumann-boundary`
- **Stage:** 3-formalized
- **Type:** SOURCE CORRECTION / EXACT FRONTIER REDUCTION / RH CRITERION
- **Scientific status:** `[FORMALIZED] [FULLY PROVEN ON PAPER] [SOURCE-SPECIFIC] [NOVELTY NOT EXTERNALLY AUDITED] [NOT AN RH PROOF]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, Sections 8.2--8.3.
- **Lean module:** `GaloisForLFunctions.RHTower.SuzukiExteriorPoleTomography`

## Result

Suzuki's printed Section 8.3 factorization is algebraically self-referential: after defining
`hhat_±=ghat vhat_±`, it places the original `vhat` bracket, rather than the `hhat` bracket, behind
the factor `ghat^{-1}`. Correct substitution gives a division-free identity with the `h` channels.

For the shifted centered Xi target

```text
R_eta(z) = z^2 XiC(z) / (XiC'(z)-eta XiC(z)),
G_eta(z) = R_eta(z)^(-1),
```

let `W` be one entire Suzuki characteristic function and `I` any entire finite-interval
contribution. The corrected exterior remainder is

```text
E_eta,W,I(z) = G_eta(z) W(z) - I(z).
```

At every Xi zero `z0`, provided `W(z0) != 0`, the remainder has an unavoidable simple pole:

```text
ord_z0 E_eta,W,I = -1,
TC_z0 E_eta,W,I = m W(z0) / z0^2,
m = ord_z0 XiC.
```

For Suzuki's all-angle real-zero family, `W(z0) != 0` at every nonreal `z0`. Hence, for any one
unit phase and any entire interval term,

```text
RH  <=>  E_eta,W,I is holomorphic at every nonreal point.                 (RH-E)
```

This is not a proof of `(RH-E)`'s right side. It replaces an imprecise large-aperture convergence
problem by one exact source-defined theorem: prove off-real holomorphy of the exterior continuation.

## 1. Source correction

Put

```text
V_q(z) = (z-i) vhat_+(z) + q(z+i) vhat_-(z),
H_q(z) = (z-i) hhat_+(z) + q(z+i) hhat_-(z).
```

The source has `hhat_±=ghat vhat_±`, with

```text
ghat(z) = z^(-2) xi'(1/2-iz) / xi(1/2-iz).
```

Direct expansion, without division, gives

```text
ghat(z) V_q(z) = H_q(z).                                      (C0)
```

Where `ghat(z) != 0`, this is

```text
V_q(z) = ghat(z)^(-1) H_q(z).                                 (C1)
```

The printed v1 line instead keeps `V_q` on the right of `(C1)`, which would assert
`V_q=ghat^{-1}V_q`. Thus `(C0)` is the only substitution-compatible reading.

After centering and allowing the finite shift, `ghat` is `G_eta` up to the fixed source scalar.
Consequently the global corrected `h` bracket is `G_eta W`, not `R_eta W`.

## 2. Finite Neumann multiplier obstruction

Use Fourier convention

```text
Fhat(z)=int_{-a}^a f(x)e^(ixz) dx,
Uhat(z)=int_{-a}^a u(x)e^(ixz) dx.
```

Suppose `u=-f''` and `f'(a)=f'(-a)=0`. Since

```text
d/dx e^(ixz) = iz e^(ixz),
```

two integrations by parts give

```text
Uhat(z)
 = -[f'(x)e^(ixz)]_{-a}^a + iz int f'(x)e^(ixz) dx
 = iz([f(x)e^(ixz)]_{-a}^a - iz Fhat(z))
 = z^2 Fhat(z) + iz(f(a)e^(iaz)-f(-a)e^(-iaz)).                (N1)
```

The endpoint term is exact. Replacing the finite Neumann inverse by the whole-line symbol `z^-2`
without it is false.

For Suzuki's explicit zero-mean Neumann kernel

```text
N_a(x,y)=(x^2+y^2)/(4a)-|x-y|/2+a/6,
f(x)=int N_a(x,y)u(y)dy,
```

and `y in [-a,a]`, endpoint subtraction and addition give

```text
N_a(a,y)-N_a(-a,y)=y,
N_a(a,y)+N_a(-a,y)=-a/6+y^2/(2a).
```

The constant in the sum vanishes against `int u=0`. With

```text
M1=int y u(y)dy,   M2=int y^2 u(y)dy,
```

one obtains

```text
f(a)-f(-a)=M1,
f(a)+f(-a)=M2/(2a),
Uhat-z^2 Fhat=iz M1 cos(az)-z M2 sin(az)/(2a).                 (N2)
```

Thus the complete finite-Neumann Fourier defect is rank two in source moments.

## 3. Interior first-order cancellation

On `[-a,a]`, Suzuki identifies

```text
h_+(x)=e^x+i,   h_-(x)=e^(-x)-i.
```

Therefore

```text
i(h_+'-h_+)=1,
i(h_-'+h_-)=1.                                                (P1)
```

At phase `q=-1`, the known interior first-order source cancels pointwise:

```text
i(h_+'-h_+) - i(h_-'+h_-)=0.                                 (P2)
```

The finite-interval Fourier bracket still has endpoint flux because cutting the transform creates
boundary distributions. Globally, distributional differentiation glues those endpoints to the
exterior. The positive survivor is therefore not an aperture clock estimate: it is the exterior
continuation carrying the corrected bracket.

## 4. Pole-transfer theorem

Let `z0` be a zero of `XiC` of multiplicity `m>=1`. Existing shifted-target factorization proves

```text
ord_z0 R_eta = 1,
TC_z0 R_eta = z0^2/m.                                        (T1)
```

Also `z0 != 0`, since `XiC(0) != 0`. Taking the meromorphic inverse in `(T1)` gives

```text
ord_z0 G_eta = -1,
TC_z0 G_eta = m/z0^2.                                        (T2)
```

If `W` is analytic and `W(z0)!=0`, then `ord_z0 W=0`, so multiplication yields

```text
ord_z0(G_eta W)=-1,
TC_z0(G_eta W)=m W(z0)/z0^2.                                 (T3)
```

An analytic `I` has order at least zero. Unequal-order subtraction cannot cancel the lowest-order
term. Therefore `(T3)` remains true for `E_eta,W,I=G_eta W-I`. This proves pole order and exact
coefficient.

## 5. RH equivalence

Fix a unit phase `q`. Suzuki's all-angle theorem says every zero of `W_q` is real. Thus at a
nonreal Xi zero `z0`, `W_q(z0)!=0`; Section 4 forces a simple pole of `E_eta,W_q,I`.

If RH holds, every Xi zero is real. At a nonreal point, `XiC(z)!=0` and `z!=0`, so

```text
G_eta(z)=(XiC'(z)-eta XiC(z))/(z^2 XiC(z))
```

is analytic. Entire `W_q` and `I` then make `E_eta,W_q,I` analytic. Conversely, if this remainder
is analytic at every nonreal point, Section 4 excludes every nonreal Xi zero. The centered
zero-locus criterion for RH finishes `(RH-E)`.

## Hostile audit

- [x] Checked raw v1 TeX: source defines `hhat_±=ghat vhat_±` immediately before the inconsistent
      repeated-`vhat` bracket.
- [x] Kept division-free identity `(C0)` primary; `(C1)` explicitly requires `ghat!=0`.
- [x] Verified Fourier sign twice: `(iz)^2=-z^2`, hence the bulk term in `(N1)` is `+z^2 Fhat`.
- [x] Verified both Neumann endpoint identities using `|a-y|=a-y` and `|-a-y|=a+y` on the interval.
- [x] Used zero mean only for the constant term in the endpoint sum.
- [x] Distinguished cut-interval endpoint flux from global distributional differentiation.
- [x] Did not identify the distinguished phases with parity beyond what the formal project proves.
- [x] Did not assume simple Xi zeros: arbitrary multiplicity is preserved in the residue.
- [x] Entire interval subtraction cannot cancel a negative-order term.
- [x] Classified integrations by parts and local meromorphic algebra as standard; novelty claim is
      limited to source correction and source-specific exterior pole localization/criterion.

## Frontier opened

The remaining theorem is concrete:

> Construct Suzuki's actual exterior-supported `h` channel independently from the Xi quotient and
> prove that its meromorphic continuation has no nonreal poles.

By `(RH-E)`, that theorem is equivalent to RH once source identification is complete. Large-aperture
estimates of the known interior term cannot establish it; a genuine exterior continuation or
positive-operator cancellation law is required.

## No-go closure

- **Killed route:** bare finite-interval `z^-2` multiplier and interior-clock convergence.
- **Killing mechanism:** exact endpoint flux `(N1)` and global exterior gluing.
- **Strongest survivor:** off-line Xi zeros are simple, multiplicity-weighted poles of the exterior
  channel, with coefficient `m W(z0)/z0^2`.
- **Lean status:** direct Lean check, exact module build, formal lint, and axiom audit pass.
