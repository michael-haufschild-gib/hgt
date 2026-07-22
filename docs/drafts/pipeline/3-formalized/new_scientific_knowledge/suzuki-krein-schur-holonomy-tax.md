# Suzuki Krein Schur holonomy tax

- **ID:** `suzuki-krein-schur-holonomy-tax`
- **Stage:** 3 — formalized scalar core
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper:** `../../2-fully-proven/new_scientific_knowledge/suzuki-krein-schur-holonomy-tax.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SuzukiAffineResolventKreinDefect.lean`

Lean proves:

```text
a x^2+2bxy+(c-n)y^2
=a(x+(b/a)y)^2+(c-n-b^2/a)y^2,

a>0 -> [(forall x y, Q(x,y)>=0) iff n+b^2/a<=c].
```

It also proves nonzero coupling gives strict tax and plugs exact negative Suzuki affine-resolvent
defect into threshold.  No RH premise, axiom, computation, or unproved source positivity appears.
