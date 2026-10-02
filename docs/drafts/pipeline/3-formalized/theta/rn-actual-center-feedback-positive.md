# RN-P-7h: actual positive Schur feedback at every center-anchored pair

Status: formalized in `ThetaTwoNodeCenterFeedback.lean`, with the signed
integral supplied by `ThetaTwoNodeSignedSturmEnergy.lean`. Both targeted
`lake --old build` commands and final `lake env lean` leaf audits pass;
direct audits emit no diagnostics. All 26 public theorems use only
`propext`, `Classical.choice`, and `Quot.sound`. Both leaves are wired into
RHTower. This rejects a sign shortcut, not RN's compensated barrier.

## Corpus basis and exact argument

`ThetaTailTwoPoint.diagonal_tail_lt_source_square` proves

    (p(z)/z) H(z,z) < k(z)²             (z>0).

The complete two-node determinant D is strictly positive. Direct inversion
of the actual Gram matrix gives, for either ordered choice of distinct nodes,

    α(x,z) = k(x)²/H(x,x)
      + (H(x,x)k(z)-H(x,z)k(x))²/(H(x,x) D).

Hence α(0,z)≥k(z)²/H(z,z)>p(z)/z=s(0,z,0) for **every z>0**.
All coefficients are the literal inverse-Gram source representer.
No limiting argument or arbitrary projection coefficients are involved.

The exact signed-energy identity in RN-P-7g then forces

    ∫₀∞ w(0,z,t) G(0,z,t)² dt < 0       (z>0).

This strengthens the initial near-center conjecture to the entire positive
center-anchored family. The earlier strict center-tail argument
`p'(0) H(0,0)<k(0)²` remains a paper observation, but is unnecessary for this
stronger proof and is not being formalized merely as extra infrastructure.

## Positive survivor and frontier consequence

The survivor is the exact inverse-Gram square decomposition and a negative
signed-energy direction made from actual coefficients. The complementary
old-span packet `k(z)k(t)-k(0)k(z+t)` vanishes at the source endpoint; its
signed energy equals its strictly positive full-tail energy. Thus the signed
form has both signs even on the actual two-node span.

The actual first-axis barrier still requires `(α-s) B < k(y) E` at the
actual residual boundary `A=0, B>0`. Positive feedback alone neither
constructs such a boundary nor violates that compensation inequality.
Arbitrary-rank positivity and the unconditional RH endpoint remain open.
