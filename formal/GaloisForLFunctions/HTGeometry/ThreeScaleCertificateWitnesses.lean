import GaloisForLFunctions.HTGeometry.FiniteDimensionalLinearQuadraticHolographicCompressionLocalityUniversalityLaw
import GaloisForLFunctions.HTGeometry.MembraneLocalityWitnesses

/-!
# The three-scale certificate on total membranes

Total membranes cover every law pair, so the three membrane-locality premises of the three-scale
holographic law are free and the three valence bounds are the ambient rank.  What remains is exactly
the geometric input — projective smoothness of the Waring form — which the Fermat form supplies in
every degree.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u w

variable {K : Type u} [Field K] [CharZero K]
  {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {d s : ℕ} [NeZero d] [Fact (1 < d)]
  {Hbase Hlin Hquad : Type*} [Fintype Hbase] [Fintype Hlin] [Fintype Hquad]

/-- **Three-scale certificate on total membranes.**  With total membranes the locality interfaces are
automatic and the certificate needs only projective smoothness of the Waring form. -/
theorem finiteDimensionalSmoothWaring_threeScaleCertificate_of_totalMembranes
    [Nonempty Hbase] [Nonempty Hlin] [Nonempty Hquad]
    (hrank : 4 ≤ Module.finrank K V)
    (q : K) (hq : IsPrimitiveRoot q d) (hd : 3 ≤ d)
    (a : Matrix (Fin s) (Fin (Module.finrank K V)) K)
    (hsmooth : MvPolynomialProjectivelySmooth (mvWaringPolynomial d a)) :
    FiniteDimensionalSmoothWaringThreeScaleCertificate q hq.pow_eq_one a
      (fun _ : Hbase => (Finset.univ : Finset (Fin (Module.finrank K V))))
      (fun _ : Hlin => (Finset.univ : Finset (Fin (Module.finrank K V))))
      (fun _ : Hquad => (Finset.univ : Finset (Fin (Module.finrank K V))))
      (Module.finrank K V) (Module.finrank K V) (Module.finrank K V) :=
  finiteDimensionalSmoothWaring_threeScaleHolographicUniversality hrank q hq hd a hsmooth
    _ _ _ _ _ _
    (membraneLocalPrincipalBrackets_univ_support _)
    (membraneLocalPrincipalBrackets_univ_support _)
    (membraneLocalPrincipalBrackets_univ_support _)
    (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)

end

end GaloisForLFunctions.HTGeometry
