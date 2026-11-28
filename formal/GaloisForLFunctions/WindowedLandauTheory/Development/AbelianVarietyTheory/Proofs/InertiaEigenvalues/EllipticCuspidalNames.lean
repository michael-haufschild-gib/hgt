import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDeterminationOnEllipticClasses
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenFromCuspidalMultisets
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-! The Green formula on elliptic classes gives cuspidal character names.
Full-degree multiplication matrices realize every elliptic test. -/

noncomputable section

open Polynomial Matrix GlobalTheory.GLq GlobalTheory.Published

namespace GlobalTheory.EllipticCharacters

theorem leftMulMatrix_charpoly_of_fullDegree {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {n : ℕ} (b : Module.Basis (Fin n) F K) (x : K)
    (hd : (minpoly F x).natDegree = n) :
    (Algebra.leftMulMatrix b x).charpoly = minpoly F x := by
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h0 : aeval x (Algebra.leftMulMatrix b x).charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx) (Matrix.charpoly_monic _)
    (minpoly.dvd F x h0) (by rw [Matrix.charpoly_natDegree_eq_dim, hd, Fintype.card_fin])

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

/-- The regular character name read from the elliptic values of a class function. -/
def HasEllipticName (θ : Kˣ →* ℂˣ) (χ : Gn g n → ℂ) : Prop :=
  ∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ,
    aeval (z : K) (y : Mt g n).charpoly = 0 →
    χ y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ)

theorem exists_ellipticName_of_isCusp (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    (χ : Gn g n → ℂ) (hc : IsCusp χ) :
    ∃ θ : Kˣ →* ℂˣ, IsRegularChar g n θ ∧ HasEllipticName θ χ := by
  obtain ⟨τ, hτ, -, hex⟩ := GlobalTheory.greenRegularCharacters g n hn K hd
  obtain ⟨θ, hθ, rfl⟩ := hex χ hc
  exact ⟨θ, hθ, (hτ θ hθ).2.2⟩

theorem exists_frobeniusPower_of_ellipticNames
    (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    {θ ψ : Kˣ →* ℂˣ} (hθ : IsRegularChar g n θ) (hψ : IsRegularChar g n ψ)
    {χ : Gn g n → ℂ} (hχ : HasEllipticName θ χ) (hχ' : HasEllipticName ψ χ) :
    ∃ j < n, ψ = θ ^ g ^ j := by
  apply exists_frobeniusPower_of_elliptic_sums_eq hn hd θ ψ hθ hψ
  intro z hz
  haveI : FiniteDimensional (ZMod g) K := Module.finite_of_finrank_pos (hd ▸ hn)
  let b : Module.Basis (Fin n) (ZMod g) K := Module.finBasisOfFinrankEq _ _ hd
  let y : Gn g n := Units.map (Algebra.leftMulMatrix b).toMonoidHom z
  have hy : (y : Mt g n).charpoly = minpoly (ZMod g) (z : K) :=
    leftMulMatrix_charpoly_of_fullDegree b z hz
  have hyr : Irreducible (y : Mt g n).charpoly := hy.symm ▸ minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
  have hyz : aeval (z : K) (y : Mt g n).charpoly = 0 := by rw [hy, minpoly.aeval]
  have h := (hχ y hyr z hyz).symm.trans (hχ' y hyr z hyz)
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h

theorem eq_cuspidal_of_same_ellipticName
    (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    {θ : Kˣ →* ℂˣ} (hθ : IsRegularChar g n θ) {χ χ' : Gn g n → ℂ}
    (hc : IsCusp χ) (hc' : IsCusp χ') (hχ : HasEllipticName θ χ) (hχ' : HasEllipticName θ χ') :
    χ = χ' := by
  obtain ⟨τ, hτ, hinj, hsurj⟩ := GlobalTheory.greenRegularCharacters g n hn K hd
  have heq {χ : Gn g n → ℂ} (hc : IsCusp χ) (hnm : HasEllipticName θ χ) : χ = τ θ := by
    obtain ⟨η, hη, rfl⟩ := hsurj χ hc
    have hη' : HasEllipticName η (τ η) := (hτ η hη).2.2
    exact (hinj θ η hθ hη).mpr
      (exists_frobeniusPower_of_ellipticNames hn hd hθ hη hnm hη') |>.symm
  exact (heq hc hχ).trans (heq hc' hχ').symm

theorem HasEllipticName.of_residueEquiv {K' : Type} [Field K'] [Algebra (ZMod g) K']
    (e : K ≃+* K') {θ' : K'ˣ →* ℂˣ} {χ : Gn g n → ℂ} (hχ : HasEllipticName θ' χ) :
    HasEllipticName (θ'.comp (Units.map e.toRingHom.toMonoidHom)) χ := by
  let eA : K ≃ₐ[ZMod g] K' := AlgEquiv.ofRingEquiv fun x =>
    RingHom.congr_fun (RingHom.ext_zmod (e.toRingHom.comp (algebraMap (ZMod g) K))
      (algebraMap (ZMod g) K')) x
  intro y hy z hz
  let z' := Units.map e.toRingHom.toMonoidHom z
  have hz' : aeval (z' : K') (y : Mt g n).charpoly = 0 := by
    have he := Polynomial.aeval_algHom_apply eA.toAlgHom (z : K) (y : Mt g n).charpoly
    rw [hz, map_zero] at he
    exact he
  rw [hχ y hy z' hz']
  simp only [MonoidHom.comp_apply, z', map_pow]

end GlobalTheory.EllipticCharacters
