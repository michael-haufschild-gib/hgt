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

Dependency-closed argument being formalized:
1. Reflection permutes the eigenvalue list, so the two cross sums agree. Expanding the
   even and odd squares gives W+C=P with C=O*O and P=E*E, both positive semidefinite.
2. The odd evaluation matrix factors through pairValue(z,beta_j), z in the distinct outer
   spectrum. Inner rows are negatives of reflected outer rows; unit-circle rows vanish.
   Hence rank C <= number of outer points, on every window, coherently under restriction.
3. On a spectrum-complete window, ACS gives negative index(W)=number of outer points.
   The existing finite-rank perturbation bound forces every positivity-producing correction
   to have at least that rank. Our C attains the bound.
4. Interpolation realizes each antisymmetric pair-value function. Its even evaluation
   vanishes, while its odd energy is strictly positive. On this vector W+tC=(t-1)C;
   therefore t<1 fails for every nonunitary datum. For t>=1 positivity follows by adding
   (t-1)C to P. For unitary data C=0.
5. Completing G by [[J,B],[B*,B*JB-G]] makes its positive index 1+negative index(G).
   Thus the same correction, subtracted only from the graph block, restores Hodge index
   without changing either pole coupling. Its scalar threshold is independent of B.

Further corpus comparison: RHTower/PaperRestrictedWeilInertia already gives abstract
minimum-rank negative-part corrections for restricted-Weil aperture operators. Our theorem
must not claim generic minimum-rank repair as new. Its content is the explicit coherent
reflection correction, half the existing Frobenius defect, and its exact Hodge threshold.
