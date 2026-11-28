import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EllipticNameFrobenius

/-! The orbit polynomial read from a cuspidal character is independent
of the regular name and of the isomorphic residue field used to read it. -/

noncomputable section

open Polynomial GlobalTheory.GLq GlobalTheory.Published

namespace GlobalTheory.EllipticCharacters

variable {p n : ℕ} [Fact p.Prime]
  {K L : Type} [Field K] [Field L] [Algebra (ZMod p) K] [Algebra (ZMod p) L]

theorem orbitPolynomial_eq_of_equiv_of_ellipticNames
    (hn : 0 < n) (hd : Module.finrank (ZMod p) K = n)
    (e : K ≃+* L) (θ : Kˣ →* ℂˣ) (θ' : Lˣ →* ℂˣ)
    (hθ : IsRegularChar p n θ) (hθ' : IsRegularChar p n θ')
    (χ : Gn p n → ℂ) (hχ : HasEllipticName θ χ) (hχ' : HasEllipticName θ' χ)
    (z : Kˣ) :
    ∏ j ∈ Finset.range n, (X - C ((θ' ((Units.map e.toRingHom.toMonoidHom z) ^ p ^ j) : ℂˣ) : ℂ)) =
      ∏ j ∈ Finset.range n, (X - C ((θ (z ^ p ^ j) : ℂˣ) : ℂ)) := by
  let ψ := θ'.comp (Units.map e.toRingHom.toMonoidHom)
  obtain ⟨j, -, hj⟩ : ∃ j < n, ψ = θ ^ p ^ j :=
    exists_frobeniusPower_of_ellipticNames hn hd hθ (regular_comp_residueEquiv e hθ') hχ
      (hχ'.of_residueEquiv e)
  have hm : ∏ k ∈ Finset.range n, (X - C ((θ' ((Units.map e.toRingHom.toMonoidHom z) ^ p ^ k) : ℂˣ) : ℂ)) =
      ∏ k ∈ Finset.range n, (X - C ((ψ (z ^ p ^ k) : ℂˣ) : ℂ)) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [ψ, MonoidHom.comp_apply, map_pow]
  rw [hm, hj]
  exact orbitPolynomial_frobeniusPower hn hd θ z j

end GlobalTheory.EllipticCharacters

#print axioms GlobalTheory.EllipticCharacters.orbitPolynomial_eq_of_equiv_of_ellipticNames
