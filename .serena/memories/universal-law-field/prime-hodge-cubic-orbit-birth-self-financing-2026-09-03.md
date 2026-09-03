# ULF-PCOB-001 (2026-09-03)

Paper theorem: `docs/drafts/pipeline/2-fully-proven/universal-law-field/source-generated-orbit-gramian-mechanics/prime-hodge-cubic-orbit-birth-faithfulness-and-self-financing-law.md`.

For d>0, let lambda_p=log p, mu_d normalized transported Stokes weight, b_d(p)=sqrt(mu_d(p))*lambda_p^(3/2), L e_p=lambda_p e_p. The weighted reachability map has columns `2 b_d(p) r exp(-r lambda_p)` and Gram
`A_d(p,q)=8 b_d(p)b_d(q)/(lambda_p+lambda_q)^3`, exactly the corpus prime formation kernel. Joint `T_d=Phi tensor A_d=R_d R_d*`; signed homotopy is sign(t)T_|t|.

New laws:
- cubic Sylvester birth: `S_L^3(A_d)=8|b_d><b_d|`; joint `S_(I tensor L)^3(T(t))=8 sign(t) Phi tensor |b><b|`; unique bounded solution;
- 2x2 nilpotent Jordan lift `[L -I;0 L]` converts weighted orbit into ordinary first-order Lyapunov Gramian;
- PNT/log-moment proof gives b_d in ell2; coherent totality plus Dirichlet-series least-prime argument makes reachability and adjoint injective, hence T faithful compact with dense nonclosed range and proper inverse form;
- polar factorization: T interpreted as defect has infinite capital (control is unitary); D=T^2 has unique control R* and exact least HS capital `Tr T=1`;
- hostile no-go: normalized weights satisfy d log p => density 2e^-2y dy, so `||[L,A_d^2]||_HS >= c/d`; joint commutator diverges. D cannot satisfy asymptotic-invariance selector. Surviving mechanism is covariant transport of the inhomogeneous cubic boundary charge.

Failed cards:
- `integral-gramian-itself-has-finite-formation-capital.md`
- `self-financing-prime-hodge-square-is-asymptotically-source-invariant.md`

Exact RH edge: construct pre-divisor completion that transports T and T^2 multiplicatively/capital-nonincreasingly and transports cubic boundary charge; prove nonzero vertical relation horizon has infinite transported cubic-orbit capital. Do not rediscover ordinary asymptotic commutation for T^2.

No Lean written/built in this audit pass. Existing T is formalized in `PrimeHodgeHistoryIntegralNuclearHomotopyDefect.lean` and wired at RHTower umbrella line 7238.