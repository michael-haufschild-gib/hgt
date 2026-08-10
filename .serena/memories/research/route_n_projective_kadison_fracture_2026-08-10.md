# Route N C20 projective/Kadison fracture dictionary (2026-08-10)

Formal module: `formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnProjectiveKadisonFracture.lean` (umbrella-wired).

Let `D_t(p)=1-p^(-2|t|)`, complement of transverse modular cocycle.

Lean-closed exact dictionary:
- `D_t(p)=-sign(t) p Q_t(p)` (oriented linear Krein fracture).
- `H_t(p)=D_t(p)^2/[p(1+p^(-|t|))^2]` (Kakutani numerator).
- `L_t(p)=D_t(p)^2(p-1)/[p(1+p^(-|t|))^2(p+p^(-2|t|))]` (literal projective Weyl leakage).
- `log(1-D_t(p))/(2 log p)=-|t|` (exact grade recovery).
- `D_t(p)=0 iff t=0`; `D_t(p) in [0,1)`.

Verification:
- direct `lake env lean` passed;
- explicit olean generation passed;
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

Research consequence:
Route N Krein, Kakutani, Wold, projective, and Poisson/Kadison reporters are linear/quadratic shadows of one duality-adjunction fracture, not independent constraints. No further scalar reporter can force vanishing. Live arithmetic theorem is pre-divisor naturality: functional-equation inverse transport must equal positive Fourier-Mellin adjoint transport on source-landed unit-flat squarefree Xi conormal. This is zero complementary record / multiplicative-domain purity; it cannot be assumed.

Paper/map updated with (N.40)-(N.43).