import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EllipticCuspidalNames
import Mathlib.RepresentationTheory.FinGroupCharZero

/-! Schur's lemma makes the center act by a scalar on a cuspidal
representation. Evaluating at a nonzero elliptic character value
identifies that scalar with the regular character on base units. -/

noncomputable section

open CategoryTheory Polynomial Matrix GlobalTheory.GLq GlobalTheory.Published

namespace GlobalTheory.EllipticCharacters

private theorem scalar_comm {g n : ℕ} [Fact g.Prime] (c : (ZMod g)ˣ) (x : Gn g n) :
    GeneralLinearGroup.scalar (Fin n) c * x = x * GeneralLinearGroup.scalar (Fin n) c := by
  ext i j
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, mul_comm]

private theorem schur_scalar {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) [Simple τ] (s : G)
    (hs : ∀ x : G, s * x = x * s) : ∃ l : ℂ, ∀ v : τ, τ.ρ s v = l • v := by
  let F : τ ⟶ τ := ⟨FGModuleCat.ofHom (τ.ρ s), fun x => by
    ext v
    change τ.ρ s (τ.ρ x v) = τ.ρ x (τ.ρ s v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hs]⟩
  obtain ⟨l, hl⟩ := endomorphism_simple_eq_smul_id ℂ F
  refine ⟨l, fun v => ?_⟩
  have : F.hom.hom.hom v = l • v := by rw [← hl]; rfl
  exact this

private theorem natDegree_smul {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (c : Fˣ) (x : K) : (minpoly F (algebraMap F K c * x)).natDegree = (minpoly F x).natDegree := by
  have hE : IntermediateField.adjoin F {algebraMap F K c * x} = IntermediateField.adjoin F {x} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F x)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h : algebraMap F K (c⁻¹ : Fˣ) * (algebraMap F K c * x) = x := by
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      have hm := mul_mem (IntermediateField.algebraMap_mem
        (IntermediateField.adjoin F {algebraMap F K c * x}) ((c⁻¹ : Fˣ) : F))
        (IntermediateField.mem_adjoin_simple_self F (algebraMap F K c * x))
      rwa [h] at hm
  rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x), hE]

theorem central_character_of_ellipticName {g n : ℕ} [Fact g.Prime]
    (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K] (hK : Module.finrank (ZMod g) K = n)
    (τ : FDRep ℂ (Gn g n)) (θ : Kˣ →* ℂˣ) (hcusp : IsCusp τ.character)
    (hreg : IsRegularChar g n θ) (hnames : HasEllipticName θ τ.character)
    (c : (ZMod g)ˣ) (v : τ) :
    τ.ρ (GeneralLinearGroup.scalar (Fin n) c) v =
      (θ (Units.map (algebraMap (ZMod g) K).toMonoidHom c) : ℂ) • v := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hn)
  haveI : Simple τ := by
    obtain ⟨V, hV, hch⟩ := hcusp.2.1
    rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
    simpa only [hch] using hV
  obtain ⟨l, hl⟩ := schur_scalar τ (GeneralLinearGroup.scalar (Fin n) c)
    (scalar_comm c)
  obtain ⟨z, hzdeg, hS⟩ := exists_fullDegree_unit_sum_ne_zero hn hK θ hreg
  let b : Module.Basis (Fin n) (ZMod g) K := Module.finBasisOfFinrankEq _ _ hK
  let L : Kˣ →* Gn g n := Units.map (Algebra.leftMulMatrix b).toMonoidHom
  let cK : Kˣ := Units.map (algebraMap (ZMod g) K).toMonoidHom c
  let z' : Kˣ := cK * z
  have hz' : (z' : K) = algebraMap (ZMod g) K c * z := rfl
  have hy : ((L z : Gn g n) : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b z := rfl
  have hsy : ((GeneralLinearGroup.scalar (Fin n) c * L z : Gn g n) : Matrix (Fin n) (Fin n) (ZMod g))
      = Algebra.leftMulMatrix b z' := by
    rw [Units.val_mul, hy, hz', map_mul, AlgHom.commutes]
    ext i j
    simp [GeneralLinearGroup.scalar, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
  have hchar : ∀ (w : Kˣ), (minpoly (ZMod g) (w : K)).natDegree = n → ∀ M : Gn g n,
      (M : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b w →
      τ.character M = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (w ^ g ^ j) : ℂ) := by
    intro w hw M hM
    have hc : (M : Matrix (Fin n) (Fin n) (ZMod g)).charpoly = minpoly (ZMod g) (w : K) := by
      rw [hM]
      exact leftMulMatrix_charpoly_of_fullDegree b w hw
    refine hnames M ?_ w ?_
    · rw [hc]
      exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
    · rw [hc]
      exact minpoly.aeval _ _
  have hz'deg : (minpoly (ZMod g) (z' : K)).natDegree = n := by
    rw [hz', natDegree_smul]
    exact hzdeg
  have h1 := hchar z hzdeg (L z) hy
  have h2 := hchar z' hz'deg _ hsy
  have hρ : τ.ρ (GeneralLinearGroup.scalar (Fin n) c) = l • (1 : Module.End ℂ τ.V) :=
    LinearMap.ext fun w => by rw [hl]; simp
  have h3 : τ.character (GeneralLinearGroup.scalar (Fin n) c * L z) = l * τ.character (L z) := by
    simp only [FDRep.character, map_mul, hρ, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  have hcpow : ∀ j : ℕ, cK ^ g ^ j = cK := by
    intro j
    ext
    simp [cK, Units.val_pow_eq_pow_val, ← map_pow, ZMod.pow_card_pow]
  have hsum : ∑ j ∈ Finset.range n, (θ (z' ^ g ^ j) : ℂ)
      = (θ cK : ℂ) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [z', mul_pow, hcpow, map_mul, Units.val_mul]
  rw [h1, h2, hsum] at h3
  have hne : ((-1 : ℂ) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hS
  have hl' : l = (θ cK : ℂ) := by
    symm
    apply mul_right_cancel₀ hne
    simpa only [mul_left_comm (θ cK : ℂ)] using h3
  rw [hl, hl']

end GlobalTheory.EllipticCharacters
