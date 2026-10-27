# The half-defect repair of a Frobenius window

Status: research and formalization. No unproved arithmetic input is to be assumed.

Bridge: ArithmeticPolarization decomposes the reflected form into a positive collided form
minus its off-circle defect. ArithmeticCastelnuovoSeveri counts the negative directions of a
Frobenius window exactly once it contains the spectrum. ALG supplies the Hodge-index meaning
of one positive square and domination by semidefinite corrections.

Target: an explicit coherent positive correction C_n of the actual reflected evaluation Gram,
with C_n equal to half the usual off-circle defect; prove W_n+C_n is positive semidefinite.
At every spectrum-complete window, prove rank C_n is the number of distinct outer eigenvalues,
and every correction producing positivity has at least this rank. Establish the exact scalar
threshold: W_n+t C_n is positive semidefinite iff the datum is unitary or t>=1.
Transfer this to a pole-preserving Hodge repair of the completed intersection form.

Construction: for reflected eigenvalues r(z)=1/conj(z), set
A_(k,j)=conj(beta_j^k+r(beta_j)^k)/2,
B_(k,j)=conj(beta_j^k-r(beta_j)^k)/2.
Then W_n+B B*=A A*. Reflection-invariant multiplicities follow from the existing permutation.
The columns of B lie in the span of differences indexed by distinct outer eigenvalues;
hence rank(B B*)<=outer-count. The existing Pontryagin law and finite-rank perturbation bound
give the reverse inequality. Antisymmetric Lagrange interpolants prove scalar sharpness.

Novelty boundary: the original full defect/collided decomposition, exact window negative index
and general rank lower bound already exist. The new contribution must be the explicit
half-defect construction, its attaining minimal rank, exact coefficient threshold and
pole-preserving Hodge interpretation, not a restatement of the lower bound.

Scope: this is a spectral calibration and sharp repair law, not an arithmetic producer of
positivity for the unmodified Weil form. The correction uses the given spectrum and changes
the pairing. No RH or purity conclusion may be inferred from positivity of the repaired form.
