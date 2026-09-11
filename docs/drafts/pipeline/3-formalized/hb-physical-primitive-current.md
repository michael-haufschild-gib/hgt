# HB: physical primitive, original traces and complete-source current

Stage: 3-formalized. Ten new public theorems passed scratch checking, an exact-module build and their axiom audit. RH and fixed-clock extinction remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Actual objects and proved identities

Let U be `causalJointForcedResponse`, N its proved native continuous representative, and F the actual `causalCuspSourceVector`, retaining all three principal cutoff channels. All vectors use the original radial/modular product-measure Hilbert space. Define

W(t)=∫₀ᵗ(t−u)U(u)du, V(t)=∫₀ᵗU(u)du, H(t)=∫₀ᵗ(t−u)F(u)du.

The new proof establishes, for every original source, branch, amplitude and real time:

- W is exactly the native primitive's original Hilbert class, at every time.
- W′=V and V′=N are strong Hilbert derivatives everywhere; W″=U almost everywhere.
- W belongs to the original Friedrichs domain, with AW=W+H−N. The pair (W,AW) is continuous.
- W has the literal native classical representative, its actual first and second radial derivatives and zero Dirichlet trace.
- The full native radial/angular gradient energy is integrable and equals Re⟨H−N,W⟩. This uses the proved global energy identity, including removal of the actual cusp cutoffs.

For two independently chosen original sources, define

C(t)=⟨W₁(t),V₂(t)⟩−⟨V₁(t),W₂(t)⟩.

Lean proves

C′(t)=⟨W₁(t),H₂(t)⟩−⟨H₁(t),W₂(t)⟩,

and its exact finite-time integral equals C(T), since the actual initial primitives vanish. No final-time current is set to zero.

## Proof mechanism

Almost-everywhere native/physical equality transfers both Bochner primitives at every time. The first-moment identity for the double primitive and the FTC for the continuous native response prove the strong derivatives. Native original-domain admission then transfers the operator action. Its forcing is identified with H−N by the existing complete-source Bochner theorem.

For spatial cancellation, put G=W+H−N. The original covariance identity is W=J J*G. Applying the adjoint identities to two such vectors gives ⟨W₁,G₂⟩=⟨G₁,W₂⟩. Expanding this identity cancels the spatial and mass terms in the derivative of C. Thus the finite-time source balance uses the actual original operator realization without an additional symmetry or boundary hypothesis.

## Scope of the transfer

This transfers the double time primitive and its complete cusp-residual source. It does not assert classical pointwise derivatives of the arbitrary physical representative U, transfer a derivative through a QNM limit, identify this Hilbert current with the full mixed Einstein/left-QNM current, or prove extinction. The explicit lift, pulse, cross terms and other Einstein channels still require their physical current assembly.

The current Laplace bound for U uses a coarse right half-plane. The projected physical Green theorem uses 3/2<Re(w)<2; almost-everywhere equality alone does not move an integral into that chamber. The next analytical attack is the [principal energy growth estimate](../1-in-progress/hb-principal-growth-energy.md), followed by the corresponding residual-response and Laplace transfer.

## Search and verification

Broad OR searches for graph/trace and factorization/coercivity, together with deep queries for causal profile transfer and forced Wronskian differentiation, inspected declarations, candidate lemmas, source arguments, proof ideas and ingredient groups. The index reported partial/source-only results and method freshness gaps. The scalar `WholeLineWronskianSymmetry` derivative mechanism was adapted to bounded Hilbert inner products; its vanishing-endpoint hypotheses were not imported. The Fokas–Lenells Laplace candidate concerns a different generator and does not identify the HB frequency chamber.

Broad recent arXiv searches used transmutation, extrapolation and boundary triples. [Boundary quadruples and bijective realisations of abstract Friedrichs operators (July 2026)](https://arxiv.org/abs/2607.01122) discusses parametrized boundary realizations; its abstract supplies no additional HB boundary identification. No external result is a premise of the Lean proof. No numerical experiment was run.

Module: [ThetaCuspHawkingBMPhysicalPrimitiveCurrent.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPhysicalPrimitiveCurrent.lean), namespace `RHTower.D4BMJointSource`, 243 lines. The ten public theorem names run from `physicalResponsePrimitive_eq_native` through `physicalPrimitiveCurrent_balance`; the module also defines the two physical response primitives, the complete source primitive and their current.

`lake env lean` passed on the scratch source. The final exact module build passed with two jobs and only the new leaf compiled. All ten new public theorems have exactly `propext`, `Classical.choice`, `Quot.sound`. The audited source and five cached artifacts were installed byte for byte, and the leaf was imported once by `RHTower.lean`. No umbrella or full build ran. The isolated audit uses installed dependency artifacts and only the new module as a build target.

Repository indexing completed; all fourteen public declarations appear in `LEAN_API.md`, and the umbrella import occurs once. Global formal lint passed with existing large-file warnings. Local report links were checked. Frontier map and universal-law ledger were not edited. All owned checks and searches completed; the isolated audit and owned temporary files were removed after artifact verification.
