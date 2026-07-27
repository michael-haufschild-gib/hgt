# Frobenius coherence-defect spectrum

- **ID:** `deninger-frobenius-coherence-defect-spectrum`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE
- **Label:** `DAC_FROBENIUS_COHERENCE_DEFECT_SPECTRUM`
- **Parent:** `deninger-coarse-invariant-sheaf-rost-schmid-descent`
- **Statement:** the non-scalar middle arithmetic cohomology is the
  coarse-sheaf hypercohomology of failures to glue local scalar
  Frobenius homotopies.

## Motivation

On algebraic character charts,
`DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE` gives a pure two-term real
Milnor coefficient.  On its cohomology, rational powers have scalar Tate
weight.  If this scalar action extended coherently to final cohomology,
`DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO` would force the generator to
be scalar.

The chain maps need only be locally homotopic to their scalar weights.
`DAC_LOCAL_FROBENIUS_HOMOTOPY_DEFECT` constructs the closed classes
\[
 [c_{m,n}]
 =
 [h_{mn}-F_mh_n-a_nh_m]                                             \tag{1}
\]
measuring failure of those homotopies to be multiplicatively coherent.

## Defect sheaf

Let \(\mathscr E nd^\bullet(\widetilde{\mathscr A})\) be the
endomorphism dg sheaf of the analytic Tate--Milnor coefficient on the
suspension cover.  Local homotopies \(h_n\) define a Čech/coherence class
\[
 \mathfrak c_F
 \in
 \mathbb H^1\!\left(
   X_W,
   (\pi_*\mathscr Z^{-1}\mathscr E nd
      (\widetilde{\mathscr A}))^{\mathbb Q_{>0}}
 \right),                                                            \tag{2}
\]
where \(\mathscr Z^{-1}\) denotes closed degree \(-1\) endomorphisms,
modulo homotopy coboundaries and the cocycle relation `(5)` of the paper
theorem.

The target in `(2)` is a chartwise representative.  Its source-native
global target is the degree-one Leray edge of
`DAC_ARITHMETIC_PROJECTION_LERAY_ROST_SCHMID_RESOLUTION`; no
coarse-to-derived quotient-stack cone is used.

## Conjecture

`[CONJECTURE] [DAC_FROBENIUS_COHERENCE_DEFECT_SPECTRUM]`

1. The local scalar homotopies exist on the quotient-adapted pro-Stein
   chart basis.
2. Their defect classes descend through
   `DAC_FINITE_CORRESPONDENCE_ANALYTIC_REALIZATION` and are independent of
   choices.
3. They map canonically into the degree-one Leray edge and then the
   intrinsic middle hypercohomology of
   `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`.
4. In the mixed coefficient topology of
   `DAC_ADELIC_L1_L2_ROST_SCHMID_HODGE_COEFFICIENT`, its closed span,
   together with prime MW residues, is the harmonic complement of the
   scalar Kummer sector and hence supplies all nontrivial reduced
   arithmetic \(H^1\).
5. The transverse flow on `(2)` is non-scalar; its test-function trace
   localizes to the prime-power correspondence defects.
6. Vanishing of \(\mathfrak c_F\) forces the final flow to factor through
   exact pure invariants and hence triggers the scalar-spectrum no-go.

## Construction program

1. Produce explicit contracting homotopies \(h_n\) on each finite
   pro-Stein relative-cell model.
2. Compute `(1)` on overlaps and verify the cocycle relation.
3. Identify change of homotopy with a coboundary.
4. Descend the class through Galois maps, finite correspondences, and MW
   residues.
5. Prove clause 4 by the hypercover spectral sequence.
6. Relate the local trace of the defect at \(p^k\) to the oriented fixed
   correspondence.
7. Prove the defect quotient is positive for the cup--Hodge form and
   that its centered power action is non-scalar.  Positivity of the
   local adelic Kummer \(L^2\) form is insufficient.

## Falsifiers

- If all defect classes vanish coherently, this mechanism produces no
  non-scalar spectrum.
- Local nonzero representatives without choice-independence do not
  define arithmetic cohomology.
- A class manufactured from Xi zeros is circular.
- The defect trace must be derived from finite correspondences; matching
  only its support at \(k\log p\) is insufficient.
- Bare adelic \(L^2\) cannot be used to close this conjecture: its
  product-formula subspace is dense and its centered Kummer action is
  scalar by `DAC_NAIVE_ADELIC_L2_KUMMER_COMPLETION_NO_GO`.

## Current status

- Universal closed-defect and cocycle laws: paper-proved.
- Existence of local homotopies, nonvanishing, descent, generation of
  \(H^1\), and fixed-point trace: open.

**Verdict:** `ACTIVE MECHANISM CONJECTURE; PRECISE SOURCE OF NON-SCALAR
MIDDLE COHOMOLOGY ISOLATED`.

## Log

- 2026-07-26 — Extracted after reconciling local Milnor purity with the
  scalar-suspension no-go.
