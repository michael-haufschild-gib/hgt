# Cross-Gram polar reconstruction and relative-phase law

- **ID:** `nhg-cross-gram-polar-reconstruction`
- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [UNIVERSAL FIELD THEOREM] [POSITIVE OBSERVER]`
  `[PHASE QUOTIENT] [CROSS-POLAR RECONSTRUCTION] [FINITE HILBERT SECTOR]`
  `[NO ROUTE INPUT] [NOT RH] [NO LEAN WRITTEN OR BUILT]`

## 1. One positive shadow

Let `V,W` be finite-dimensional complex Hilbert spaces and let `T:V->W`. Its positive Gram shadow is

\[
 G_T=T^*T\in\operatorname{End}(V).
\tag{CG.1}
\]

### Theorem 1.1 — exact phase quotient

For maps `T:V->W` and `S:V->W'`,

\[
 T^*T=S^*S
\tag{CG.2}
\]

if and only if there is a unique partial isometry

\[
 U:\overline{\operatorname{ran}T}\longrightarrow
 \overline{\operatorname{ran}S}
\tag{CG.3}
\]

such that

\[
 S=UT.
\tag{CG.4}
\]

Thus a Gram observer forgets exactly the left polar partial isometry on the active output space. It
does not merely forget one scalar phase.

### Proof

Define `U(Tv)=Sv`. Equation `(CG.2)` gives

\[
 \|Sv\|^2=\langle v,S^*Sv\rangle
 =\langle v,T^*Tv\rangle=\|Tv\|^2.
\tag{CG.5}
\]

Hence `Tv=0` implies `Sv=0`, so `U` is well-defined and isometric on `ran T`. It extends uniquely to
the stated partial isometry and satisfies `(CG.4)`. The converse follows from `U^*U=1` on
`ran T`. QED.

## 2. A family and its cross-Gram packet

Let `V_1,...,V_N,W` be finite-dimensional complex Hilbert spaces and let

\[
 T_i:V_i\longrightarrow W.
\tag{CG.6}
\]

Define the synthesis map

\[
 \mathbf T:\bigoplus_{i=1}^N V_i\longrightarrow W,
 \qquad
 \mathbf T(v_1,\ldots,v_N)=\sum_iT_iv_i.
\tag{CG.7}
\]

Its block Gram operator has entries

\[
 (\mathbf T^*\mathbf T)_{ij}=T_i^*T_j.
\tag{CG.8}
\]

Call the family `(T_i^*T_j)_(i,j)` the **cross-Gram packet**.

### Theorem 2.1 — cross-Grams reconstruct relative phase

Let `S_i:V_i->W'` be a second family. The following are equivalent:

1. `T_i^*T_j=S_i^*S_j` for every `i,j`;
2. there is a unique partial isometry

   \[
   U:\overline{\sum_i\operatorname{ran}T_i}
   \longrightarrow
   \overline{\sum_i\operatorname{ran}S_i}
   \tag{CG.9}
   \]

   such that

   \[
   S_i=UT_i\qquad\text{for every }i.
   \tag{CG.10}
   \]

If both families jointly span their codomains, `U` is unitary. Therefore the full cross-Gram packet
recovers every relative phase and orientation allowed by Hilbert geometry, leaving only one common
output gauge.

### Proof

The block identities are exactly `mathbf T^*mathbf T=mathbf S^*mathbf S`. Apply Theorem 1.1 to the
two synthesis maps. Restriction to the `i`th summand gives `(CG.10)`. Joint spanning makes the
initial and final spaces the full codomains. QED.

## 3. Individual positivity is insufficient

Individual Gram shadows retain only the diagonal blocks `T_i^*T_i`. They permit independent left
partial isometries and lose relative phase.

### Counterexample 3.1

Take `V_1=V_2=W=mathbb C` and

\[
 T_1=T_2=1,
 \qquad
 S_1=1,\quad S_2=-1.
\tag{CG.11}
\]

Then

\[
 T_i^*T_i=S_i^*S_i=1
\tag{CG.12}
\]

for both indices, but

\[
 T_1^*T_2=1,
 \qquad
 S_1^*S_2=-1.
\tag{CG.13}
\]

No common output unitary sends both `T_i` to `S_i`. A single positive observer per tensor is
therefore insufficient; interaction/cross-polarization data are load-bearing.

## 4. Kernel, rank, and capacity

The block Gram packet also determines

\[
 \ker\mathbf T=\ker(\mathbf T^*\mathbf T),
 \qquad
 \operatorname{rank}\mathbf T=\operatorname{rank}(\mathbf T^*\mathbf T),
\tag{CG.14}
\]

and every nonzero singular value of `mathbf T`. Hence it simultaneously records joint invisible
directions and positive filling cost while forgetting only the common left partial isometry.

This is the exact finite-dimensional polar observer law required by NHG:

\[
 \boxed{
 \text{unsquared law tensors}
 \longrightarrow
 \text{cross-Gram packet}
 =\text{quotient by one common output gauge}.}
\tag{CG.15}
\]

## 5. Field consequences

1. Positivity itself is not information loss. The specified Gram observer is.
2. Independent positive shadows erase relative phase; cross-polarizations restore it.
3. A positive NHG atlas is conservative on a finite tensor family exactly when its cross-Gram
   synthesis packet is retained and the remaining common output gauge is declared.
4. Any claim that a scalar determinant or norm reconstructs an oriented law tensor is false in
   output dimension greater than one.
5. Cross-Gram reconstruction is compatible with parallel observer repair: it converts separately
   phase-blind legs into one jointly conservative polar observer.

## 6. Scope

- The theorem is finite-dimensional Hilbert linear algebra. Infinite-dimensional closed-range,
  unbounded-domain, Krein, Tate, and derived variants require separate hypotheses.
- The common partial isometry need not preserve an additional filtration, cyclic bracket, anchor,
  or source marking. Those constraints must be imposed on the gauge group separately.
- Cross-Grams do not reconstruct nonlinear `L_infinity` operations from unrelated domains unless
  they are first assembled into a typed synthesis map.
- No source selection, dynamics, holonomy, properness, or RH statement follows.

## Lean formalization status

- **Status:** `[LEAN IMPLEMENTED] [LEAF CHECK PASSED] [FINAL AXIOM/UMBRELLA AUDIT PENDING]`
- **Module:** `GaloisForLFunctions.HilbertMetric.NomologicalCrossGram`
- **Umbrella wiring:** imported by `GaloisForLFunctions.HilbertMetric`
- **Exact capstones:**
  - `gram_eq_iff_existsUnique_activeRangeIsometry`
  - `crossGramPacket_eq_iff_existsUnique_commonRangeIsometry`
  - `crossGramPacket_eq_iff_existsUnique_codomainIsometry_of_jointly_surjective`
  - `ker_gram`
  - `finrank_range_gram`
  - `gram_hasEigenvalue_sq_singularValues`
  - `support_singularValues_eq_range_rank`
  - `scalar_relative_phase_counterexample`
- **Verification:**
  `lake env lean GaloisForLFunctions/HilbertMetric/NomologicalCrossGram.lean` passed with no
  errors or warnings.
- **Promotion gate still open:** final umbrella build, project lint, and `#print axioms` audit are
  intentionally deferred to the program-wide final audit. Card remains in Stage 2.
