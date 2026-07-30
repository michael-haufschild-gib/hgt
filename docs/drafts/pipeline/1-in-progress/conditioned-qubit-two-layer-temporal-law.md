# Conditioned-qubit two-layer temporal law

- **ID:** `conditioned-qubit-two-layer-temporal-law`
- **Stage:** 1-in-progress
- **Type:** PHYSICAL WITNESS / SPECTRAL PERTURBATION / OBSERVER TIME
- **Source:** observer-time ensemble cascade law
- **Scientific status:** `[PAPER-PROVED]`
  `[EXACT PROFILES LEAN-PROVED]`
  `[AFFINE HERMITIAN HAMILTONIAN AND EIGENBRANCHES LEAN-PROVED]`
  `[MINIMUM REPLICA ORDERS LEAN-PROVED]`
  `[WALL-CROSSING COMPOSITION FINAL AUDIT OPEN]`
  `[DEVICE INTERPRETATION OPEN]`

## Question

Can one fixed, finite, local, Hermitian Hamiltonian force more than one
observer-time birth horizon, or are higher layers only an abstract
possibility of analytic spectral paths?

## Exact claim

On \(\mathbb C^3\otimes\mathbb C^2\), let the qutrit label
\(s\in\{0,1,2\}\) control a qubit block
\[
 H_s(g)=b_sI+(1+c_sg)Z+h_sgX,
 \qquad
 (c_0,c_1,c_2)=(0,1,2),\quad
 (h_0,h_1,h_2)=(1,1,2).
\]
The complete Hamiltonian
\[
 H(g)=\sum_{s=0}^2 |s\rangle\langle s|\otimes H_s(g)
\]
is affine in the coupling \(g\), two-site local, and Hermitian. Its two
eigenvalue branches in sector \(s\) are
\[
 E_{s,\pm}(g)=b_s\pm
 \sqrt{(1+c_sg)^2+h_s^2g^2}.
\]
Write \(D_s=E_{s,+}-E_{s,-}\), and define two projective spectral
characters
\[
 \delta_1=D_1-D_0,\qquad
 \delta_2=D_0-2D_1+D_2.
\]
Then, along \(g\downarrow0\),
\[
 \boxed{\frac{\delta_1(g)}g\longrightarrow2,}
 \qquad
 \boxed{\frac{\delta_2(g)}{g^2}\longrightarrow3.}
\]
Consequently the symmetric time averages of the corresponding phase
characters have exact wall crossings on different horizons:
\[
 T_1=\tau g^{-1},\qquad T_2=\tau g^{-2}.
\]
Below each horizon the character is unresolved, at its horizon it tends
to the sinc profile \(\operatorname{sinc}(2\tau)\) or
\(\operatorname{sinc}(3\tau)\), and beyond its horizon it dephases to
zero.

## Paper proof

Set
\[
 R_{c,h}(g)=\sqrt{(1+cg)^2+h^2g^2},
 \qquad D_{c,h}=2R_{c,h}.
\]
For \(g>0\), \(1+cg>0\) for the nonnegative \(c\) used here. Rationalizing
the square root gives the exact identity
\[
 R_{c,h}(g)-(1+cg)
 =\frac{h^2g^2}{R_{c,h}(g)+1+cg}.
\]
The denominator tends to \(2\), hence
\[
 \frac{R_{c,h}(g)-(1+cg)}{g^2}\longrightarrow\frac{h^2}{2}.
\]
It follows that
\[
 D_{c,h}(g)=2+2cg+h^2g^2+o(g^2).
\]
Therefore
\[
 \frac{D_{1,1}-D_{0,1}}g\longrightarrow2,
\]
and cancellation of both the constant and linear terms in
\(D_{0,1}-2D_{1,1}+D_{2,2}\) yields
\[
 \frac{D_{0,1}-2D_{1,1}+D_{2,2}}{g^2}
 \longrightarrow
 1-2+4=3.
\]
The eigenvalue formula follows because the characteristic equation of
\((1+cg)Z+hgX\) is
\[
 \lambda^2-\big((1+cg)^2+h^2g^2\big)=0.
\]
The symmetric-window wall crossings then follow from the exact identity
\[
 \frac1{2T}\int_{-T}^{T}e^{it\delta}\,dt
 =\operatorname{sinc}(T\delta).
\]

## What this would establish

This is a finite physical counterexample to the idea that every weakly
broken spectral constraint becomes visible on one universal \(g^{-1}\)
time. One affine local Hamiltonian contains two operationally distinct
temporal layers. The second is invisible on every \(g^{-r}\) window with
\(r<2\), although the coupling is already nonzero.

The two characters also have different exact replica heights. The first has
positive coefficient mass \(2\); the second has positive coefficient
mass \(4\). A general theorem now proves that positive coefficient mass is
the minimum possible replica realization order of every balanced integer
spectral character. Thus the first layer has minimum order two and the
second minimum order four. The remaining physical bridge is to prove that
the corresponding terms occur with nonzero coefficient in a stated
fidelity-moment or interferometric protocol.

## Hostile review

### “This is an engineered block diagonal toy.”

Correct. It proves physical realizability and exact multi-layer
wall-crossing, not genericity, thermalization, or many-body universality.
General-science significance requires either a natural symmetry-protected
platform or a theorem forcing arbitrarily many layers in a scalable local
family.

### “Two-site local is a semantic trick.”

The Hamiltonian is a qutrit-conditioned qubit interaction and is genuinely
local on two sites, but it has conserved qutrit sectors. Paper must state
that structure. Claiming generic interacting many-body dynamics would be
false.

### “The offsets \(b_s\) might create degeneracies.”

Choose explicit separated offsets, for example
\((b_0,b_1,b_2)=(0,4,9)\), and restrict to a proved coupling
neighborhood if a simple complete spectrum is needed. The two splitting
relations do not depend on the offsets.

### “Sinc is elementary.”

Yes. Significance can only come from one valued relation lattice forcing
an exact hierarchy of observer ensembles and rank conservation across all
characters. This witness alone is not the universal law.

### “No experiment measures an abstract character.”

Fatal unless closed. Need a low-copy interferometric or recurrence-moment
reporter with the same two exponents, including state preparation and
readout assumptions.

## Falsifiers

Reject this witness if any one holds:

1. the displayed \(6\times6\) Hamiltonian is not Hermitian or affine in
   \(g\);
2. the six displayed branches are not its eigenvalues;
3. either normalized detuning limit is not \(2\) or \(3\);
4. the corresponding actual symmetric time average does not obey its
   claimed wall crossing;
5. the second relation is already generated by a lower-replica reporter
   after all cancellations are included.

## Formal obligations

Completed:

1. Both exact normalized birth limits are Lean-proved.
2. The \(6\times6\) Hamiltonian is Lean-proved Hermitian and exactly affine
   in \(g\).
3. Every displayed branch has a Lean-proved nonzero eigenvector for every
   \(g>0\).
4. The minimum-replica law is Lean-proved for every balanced character;
   the displayed characters have exact minima two and four.

Open:

1. Prove that the six displayed branches exhaust the spectrum in one
   explicit positive-coupling neighborhood.
2. Complete the thin formal composition with the actual
   symmetric-window wall-crossing theorem in the final module audit.
3. Prove the fidelity-moment or interferometric reporter coefficient and
   state-preparation bridge.
