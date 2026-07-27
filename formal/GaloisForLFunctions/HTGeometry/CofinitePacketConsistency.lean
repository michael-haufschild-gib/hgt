import GaloisForLFunctions.HTGeometry.PrimeProfileJetPacket

/-!
# The cofinite jet packet is consistent

`CofinitePrimeProfileJetPacket g` asks, for every jet order and every finite set of forbidden primes,
for a separated packet of primes avoiding them whose jet matrix is nonsingular.  It is consumed
together with prime-power support, and neither the corpus nor the criterion
`cofinitePrimeProfileJetPacket_iff_rayTailIndependent` ever exhibits a source family satisfying it —
a characterization transfers the property without producing it.

Over the empty index the packet matrix is the empty matrix, whose determinant is `1`, so the bundle
is consistent and the pair of premises is jointly satisfiable.  This is a consistency statement at
the degenerate end and nothing more: a packet over a *nonempty* index needs the jet matrix to be
genuinely nonsingular for cofinitely many prime choices, which is the substantive content of the
layer.

* **`cofinitePrimeProfileJetPacket_empty`**, `cofinitePacket_and_support_empty`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The empty source family is a cofinite jet packet.**  Its packet matrix is the empty matrix,
with determinant `1`. -/
theorem cofinitePrimeProfileJetPacket_empty (g : Empty → ArithmeticFunction ℂ) :
    CofinitePrimeProfileJetPacket g := by
  intro m forbidden _
  refine ⟨fun x => x.1.elim, fun x => x.1.elim, fun a _ _ => a.1.elim, fun row => row.1.elim, ?_⟩
  haveI : IsEmpty (Empty × Fin (m + 1)) := ⟨fun x => x.1.elim⟩
  rw [Matrix.det_isEmpty]
  exact one_ne_zero

/-- The two premises of the packet layer are jointly satisfiable. -/
theorem cofinitePacket_and_support_empty (g : Empty → ArithmeticFunction ℂ) :
    CofinitePrimeProfileJetPacket g ∧
      ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i) :=
  ⟨cofinitePrimeProfileJetPacket_empty g, fun i => i.elim⟩

end GaloisForLFunctions.HTGeometry
