# Proof audit — generic maximal projective rank in every qudit path

- **Object audited:** `../2-fully-proven/nearest-neighbor-qudit-projective-spectral-maximality.md`
- **Audit date:** 2026-07-29
- **Status:** `[INTERNAL ADVERSARIAL AUDIT PASSED] [EXTERNAL SPECIALIST AUDIT OPEN]`
- **Claim:** for every \(n,q\geq2\), almost every arbitrary one-site plus
  nearest-neighbour two-site Hamiltonian on an open \(q\)-level chain has
  projective rational spectral rank \(q^n-1\).

## Dependency-closed attack

### 1. Does the two-site base silently assume the desired eigenbasis?

For \(n=2\), the allowed edge space is the full Hermitian matrix space on
\(\mathbb C^q\otimes\mathbb C^q\). For one endpoint \(u\) and one ordered
pair of orthonormal eigenvectors, failure of every local transition matrix
element is exactly
\[
 \operatorname{Tr}_{\bar u}|\psi_\beta\rangle
 \langle\psi_\alpha|=0.
\]
The squared Hilbert--Schmidt norm of this partial trace is a real-analytic
function on \(U(q^2)\), and it is not identically zero: map the pair to
\(|0,0\rangle,|1,0\rangle\). A finite union over pairs cannot cover the
connected analytic manifold \(U(q^2)\). A basis for which every pair is
joined therefore exists. Distinct eigenvalues then realize it as an allowed
Hamiltonian.

**Verdict:** closed. The manuscript proof must state the nonzero analytic
function explicitly; “generic eigenbasis” alone is insufficient.

### 2. Can one perturbation create all required endpoint edges?

At the product Hamiltonian, each target cross-block matrix element is an
analytic function of the finitely many edge-coupling coefficients. Its
derivative in the coefficient multiplying
\(A_{\alpha\beta}\otimes X^{rs}\) is
\[
 \frac{
 \langle\psi_\alpha,A_{\alpha\beta}\psi_\beta\rangle
 (C_s-C_r)}
 {E_\alpha+a_r-E_\beta-a_s},
\]
which is nonzero. Each target failure set is therefore a proper analytic
zero set. Their finite union cannot cover a sufficiently small coefficient
ball. Simplicity and the within-block triangle are open conditions.

**Verdict:** closed. The perturbation is chosen once outside the finite
union; the proof does not choose incompatible perturbations edge by edge.

### 3. Does second-order perturbation omit compensating terms?

For \(p=(\alpha,r)\), \(q=(\beta,s)\), the perturbation
\(A\otimes X^{rs}\) couples \(p\) only to states in the opposite level.
In the weighted sum of second eigenvalue derivatives, the two orientations
combine as
\[
 \frac{(c_{\alpha,r}-c_{\beta,s})
 |\langle\psi_\alpha,A\psi_\beta\rangle|^2}
 {z+E_\alpha-E_\beta},
 \qquad z=a_r-a_s,
\]
up to one common nonzero factor. Terms with \(\alpha=\beta\) share the pole
\(z=0\), but the proof never uses that pole.

**Verdict:** closed for every nonzero old gap.

### 4. Are the poles truly isolated?

Maximal projective rank of the old spectrum implies
\[
 E_\alpha-E_\beta=E_\gamma-E_\delta\neq0
 \Longrightarrow
 (\alpha,\beta)=(\gamma,\delta).
\]
Otherwise the equality is a nontrivial rational zero-sum relation among the
old eigenvalues. Hence every nonzero ordered gap supplies its own pole and
its residue forces
\[
 c_{\alpha,r}=c_{\beta,s}
\]
whenever some endpoint observable joins \(\alpha\) and \(\beta\).

**Verdict:** closed.

### 5. Does the equality graph connect all branches for every \(q\)?

The equality graph is the categorical product
\(\mathcal G_u(H_A)\times K_q\). A categorical product of two connected
graphs is connected exactly when at least one factor is non-bipartite.
The old endpoint graph is connected and non-bipartite by construction.
Equivalently, walks between any two old vertices exist with both parities;
choose the parity of a \(K_q\) walk and pad both walks by two-edge
backtracks until their lengths match.

**Verdict:** closed, including \(q=2\).

### 6. Does branchwise independence imply a global generic theorem?

For a fixed nonconstant rational zero-sum vector \(m\), symmetrize its
eigenvalue form over all \(D!\) labelings. The result is a polynomial in
characteristic coefficients, hence in local coupling parameters. If this
polynomial vanished identically, then on a connected simple-spectrum chart
the finite product of analytic branch factors would vanish identically.
The ring of real-analytic functions on a connected chart has no zero
divisors, so one branch factor would be an analytic identity, contradicting
the endpoint-extension lemma.

Each relation therefore lies in a proper polynomial zero set. The
discriminant adds one more. A countable union over
\(m\in\mathbb Q^D\) is null and meagre, leaving a dense full-measure
\(G_\delta\).

**Verdict:** closed. This local-to-global step must not be compressed to
“by genericity.”

### 7. Does the exact recurrence density require an unproved stochastic
assumption?

No. Projective rational independence makes the gap orbit uniquely
equidistributed on \(\mathbb T^{D-1}\). The target
\[
 \max_j|e^{-i\theta_j}-1|<\varepsilon
\]
is a Cartesian product of arcs whose normalized one-coordinate measure is
\(2\arcsin(\varepsilon/2)/\pi\). Its boundary has Haar measure zero.
Equation `(13)` follows by deterministic Kronecker--Weyl equidistribution.

**Verdict:** closed for asymptotic density. It does **not** identify an
individual first-return time.

### 8. Does “double exponential in entropy” overstate the theorem?

With \(S_{\max}=\log D=n\log q\), taking the negative logarithm of the exact
density gives
\[
 -\log\operatorname{dens}
 =
 (e^{S_{\max}}-1)
 \log\!\frac{\pi}{2\arcsin(\varepsilon/2)}.
\]
The suppression is therefore exactly exponential in \(e^{S_{\max}}\) at
fixed \(0<\varepsilon<2\).

**Verdict:** closed as a finite-chain density identity. It is not a theorem
about gravitational entropy, black-hole spectra or a finite-time waiting
distribution.

## Remaining hostile objections

1. Independent specialists must audit analytic perturbation conventions and
   the symmetrized-polynomial argument.
2. Priority remains open: continuum Schrödinger control theory already
   proves abstract generic non-resonance by related analytic methods.
3. Translation-invariant and fixed low-parameter chains are not covered.
4. Connected interaction graphs without a spanning path are not covered.
5. Exact arithmetic rank is discontinuous; operational finite-horizon
   activation has only a one-sided crossover bound.
6. Formal proof is absent. No manuscript theorem is authorized.

## Audit conclusion

No internal counterexample or missing logical dependency was found in the
path theorem. Its defensible novelty is not “generic non-resonance.” It is
the survival of full \(q^n-1\) projective rank inside a static,
bounded-degree, polynomial-parameter local many-body family, together with
its exact recurrence consequences.

Current status remains **paper proof only**.
