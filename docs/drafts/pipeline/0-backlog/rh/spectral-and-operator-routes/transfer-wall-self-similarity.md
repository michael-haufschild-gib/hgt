# The Transfer Wall: Self-Similarity of T-Averaged Spectral Certification

**Status: BACKLOG (card created 2026-07-05, from MWM docs 80–81)**

**Claim [PROVED-sketch + MEASURED, promotion = write-out + census certificates].**
For Dirichlet-type sums S(t) = Σ_{p≤X} a_p cos(t log p), every T-averaged
frequency-side certification instrument (moments, Chernoff, bandlimited
Fourier majorants) obeys ONE two-sided wall: (i) under worst-case rational
gaps the instrument is equivalent to the shared degree budget
(bandwidth × ℓ¹-mass ≤ log T); (ii) beyond it, the transfer error is exactly
the near-collision census |log(A/B)| ≤ δ over coprime prime-product pairs;
(iii) the census at δ ~ 1/T is the same species of object as the original
t-average (near-diagonal weighted prime-product sum) — the problem is
self-similar, and the recursion terminates only on arithmetically thin
generating sets (bounded prime lists: smooth-pair sparsity). Measured
two-sidedly at T = 3·10¹² (MWM docs 80 §5, 81 §2): B1 hatch open
(twin-smooth census ~1e−4), mid-prime hatches closed (SP twin census
2.65/octave, O(1)).

**Why it matters for the branch:** constraint-not-flow at the instrument
level — the obstruction to finite-height certification is an arithmetic
CONSTRAINT (thinness at scale 1/δ), not a missing estimate; and the positive
side (B1 model-grade certificate via enumerable twin-smooth censuses) is a
new instrument that certifies beyond the degree budget.

**Promotion path:** doc 81 §2 clauses W1–W3 as theorems (W1 write-out is
mechanical; W2 = census certificates via smooth enumeration + Rankin tails;
W3 = the exact self-similarity identity); Lean = Bessel-J mini-theory +
Beurling–Selberg majorants + bandlimited-transfer skeleton (none in mathlib).
