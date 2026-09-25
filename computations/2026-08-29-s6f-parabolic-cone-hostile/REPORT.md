# S6F parabolic-cone hostile test

## Question

After the computation-free parabolic trajectory bounds

```text
X > 191/10 + (147/20)w,
y > 13/32 + w/32,
0 < w=z^2 < 9/100,
```

does forced scale/ratio growth overpower adverse lambda-clock motion, making normalized projective
drift increase with `w`? If not, does a stronger completely monotone or simple outer-slack law
survive?

Diagnostic only. No coefficient, digest, corner value, or sign count in this folder is admissible in
a Lean proof.

## Computation

RunPod host: 128 CPUs, Python/SymPy environment recorded in `environment.txt`. Reconstructed exact
normalized drift `projectiveDrift/R = z*C(X,z,y)` from source-positive Lie recursion, verified that
`C` has only even powers of `z`, and set

```text
C_p(S,w) = C(191/10 + (147/20)w + S, sqrt(w), 13/32 + w/32).
```

Used power basis in `S>=0` and exact Bernstein basis on `0<=w<=9/100`. Independent verifier rebuilt
the wall and coefficient transport, compared exact SHA-256 coefficient digests, and reproduced
selected orders.

## Outcomes

- **Increasing-in-`w` conjecture is false.** `dC_p/dw` has all 651 exact Bernstein coefficients
  strictly negative. Nearby scale shears `k=0,5,6,7,147/20,15/2,8,10` in
  `X=191/10+k w+S` all have the same strict negative certificate.
- **Sharp positive survivor:** `C_p>0`, `dC_p/dS>0`, `dC_p/dw<0`, and `d²C_p/dw²>0` on the full
  half-strip. Respective exact Bernstein coefficient counts are `665`, `611`, `651`, and `637`, all
  with the asserted strict sign.
- **Complete-monotonicity escape is false.** Sign-corrected derivatives
  `(-1)^j d^j C_p/dw^j` are strictly positive for `j=0,1,2`; already `j=3` is mixed
  (`174` negative, `449` positive), and every tested order through `13` remains mixed.
- **Simple outer-slack expansion is false.** In `r=9/100-w`, ordinary coefficients of
  `C_p(S,9/100-r)` split `309` negative and `356` positive.
- Exact outer floor is positive and has negative `w` derivative. Thus the diagnostic minimum is the
  parabolic outer corner

```text
(X,z,y) = (39523/2000, 3/10, 1309/3200),
```

  not the artificial rectangular corner `(191/10,3/10,13/32)`.

Independent verification output:

```text
verified: parabolic wall is positive/decreasing/convex; alternating order 3 fails
```

## Consequences

Parabolic trajectory coupling materially sharpens S6F-PD but does not yield the hoped-for increasing
or completely monotone law. Any conceptual proof must explain exactly second-order variation:
positive, decreasing, convex, with third-order sign failure. Assuming a Stieltjes/total-positivity
hierarchy would contradict the exact third-order diagnostic.

Surviving research target is now a computation-free proof of the two combined signs
`dC_p/dS>0`, `dC_p/dw<0`, plus positivity at the displayed outer corner. This is a smaller and more
trajectory-faithful target than three independent rectangular-coordinate signs. Convexity is a
non-trivial positive invariant and may support a tangent/chord proof, but it supplies no sign by
itself. No computed output was imported into Lean.
