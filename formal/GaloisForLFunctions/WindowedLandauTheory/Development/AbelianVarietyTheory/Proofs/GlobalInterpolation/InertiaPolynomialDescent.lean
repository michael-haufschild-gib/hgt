import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.SquarefreeFrobeniusCycles
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TeichmullerLabelDatum
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypeReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterPolynomialPowers

/-! The roots of a tame inertia polynomial descend through a Teichmüller
section. Frobenius stability descends the entire multiset, with multiplicities. -/

noncomputable section

open IsLocalRing Polynomial ReciprocityTheory.Gal
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.NormalizedTypes
open WindowedLandauTheory.CyclotomicNorms.CycleTypeFiniteOrder

namespace GlobalTheory.TeichPlace

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
variable {A : ValuationSubring K} {κ : ResidueField A ≃+* Fbar p}
variable {t : Fbar p →* K}

/-- The Teichmüller section recovers a root of unity of order prime to the
residue characteristic from its reduction. -/
theorem teich_redThrough_of_pow_eq_one (ht : IsTeich A κ t) {z : K} {n : ℕ}
    (hn : 0 < n) (hpn : p.Coprime n) (hz : z ^ n = 1) :
    t (redThrough A κ z) = z := by
  have hB : z ∈ A :=
    (A.valuation_le_one_iff _).mp (valuation_eq_one_of_pow_eq_one A hn.ne' hz).le
  let x := redThrough A κ z
  have hx : x ^ n = 1 := by
    change redThrough A κ z ^ n = 1
    rw [← redThrough_pow A κ hB, hz, redThrough, dif_pos (one_mem A)]
    change κ (residue A 1) = 1
    rw [map_one, map_one]
  have htx : (t x) ^ n = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨hm, hred⟩ := ht x
  apply eq_of_reduced_root_eq A κ hn hpn htx hz
  change redThrough A κ (t x) = x
  rw [redThrough, dif_pos hm, hred]

/-- Frobenius-stable tame eigenvalues are exactly the Teichmüller lifts
of the roots of one monic polynomial over the prime field. -/
theorem existsUnique_monic_of_tame_eigenvalues (ht : IsTeich A κ t) (S : Multiset K)
    (hS : ∀ z ∈ S, ∃ n : ℕ, 0 < n ∧ p.Coprime n ∧ z ^ n = 1)
    (hfrob : S.map (fun z => z ^ p) = S) :
    ∃! f : (ZMod p)[X], f.Monic ∧ (rootsBar f).map t = S := by
  let R := S.map (redThrough A κ)
  have hR : R.map t = S := by
    change (S.map (redThrough A κ)).map t = S
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id S]
    apply Multiset.map_congr rfl
    intro z hz
    obtain ⟨n, hn, hp, hpow⟩ := hS z hz
    exact teich_redThrough_of_pow_eq_one ht hn hp hpow
  have hmap (Q : Multiset (Fbar p)) :
      (Q.map (fun x => x ^ p)).map t = (Q.map t).map (fun z => z ^ p) := by
    simp only [Multiset.map_map]
    exact Multiset.map_congr rfl (fun x _ => map_pow t x p)
  have hstable : R.map (fun x => x ^ p) = R := by
    apply Multiset.map_injective ht.injective
    rw [hmap, hR, hfrob]
  obtain ⟨f, hf, huniq⟩ := existsUnique_monic_of_frobenius_stable R hstable
  refine ⟨f, ⟨hf.1, by rw [hf.2, hR]⟩, fun q hq => huniq q ⟨hq.1, ?_⟩⟩
  exact Multiset.map_injective ht.injective (hq.2.trans hR.symm)


/-- An inertia operator of prime-to-`p` order whose (p)-th power is conjugate
to it has a unique prime-field label. -/
theorem existsUnique_label_of_tame_matrix [IsAlgClosed K] (ht : IsTeich A κ t) {N m : ℕ}
    (hm : 0 < m) (hpm : p.Coprime m) (T Φ : GL (Fin N) K)
    (hT : T ^ m = 1) (hΦ : Φ * T * Φ⁻¹ = T ^ p) :
    ∃! f : (ZMod p)[X], f.Monic ∧
      (T : Matrix (Fin N) (Fin N) K).charpoly = ((rootsBar f).map fun x => X - C (t x)).prod := by
  let M := (T : Matrix (Fin N) (Fin N) K)
  have hM : M ^ m = 1 := by
    change (T : Matrix (Fin N) (Fin N) K) ^ m = 1
    rw [← Units.val_pow_eq_pow_val, hT, Units.val_one]
  have hC : (M ^ p).charpoly = M.charpoly := by
    change ((T : Matrix (Fin N) (Fin N) K) ^ p).charpoly = _
    rw [← Units.val_pow_eq_pow_val, ← hΦ, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.charpoly_units_conj Φ M
  have hfrob : M.charpoly.roots.map (fun x => x ^ p) = M.charpoly.roots := by
    rw [← GlobalTheory.CharpolyPow.roots_charpoly_pow K N p M, hC]
  have hroots (z : K) (hz : z ∈ M.charpoly.roots) : z ^ m = 1 := by
    have he := Multiset.mem_map_of_mem (fun x => x ^ m) hz
    rw [← GlobalTheory.CharpolyPow.roots_charpoly_pow K N m M, hM] at he
    have hz' := (mem_roots (Matrix.charpoly_monic _).ne_zero).mp he
    rw [Matrix.charpoly_one, IsRoot, eval_pow, eval_sub, eval_X, eval_one] at hz'
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz')
  obtain ⟨f, hf, huniq⟩ := existsUnique_monic_of_tame_eigenvalues ht M.charpoly.roots
    (fun z hz => ⟨m, hm, hpm, hroots z hz⟩) hfrob
  refine ⟨f, ⟨hf.1, ?_⟩, fun q hq => ?_⟩
  · change M.charpoly = _
    rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (Matrix.charpoly_monic M), ← hf.2,
      Multiset.map_map]
    rfl
  · apply huniq q
    refine ⟨hq.1, ?_⟩
    rw [show M.charpoly = _ from hq.2]
    simpa only [Multiset.map_map, Function.comp_def] using
      (roots_multiset_prod_X_sub_C ((rootsBar q).map t)).symm

end GlobalTheory.TeichPlace
