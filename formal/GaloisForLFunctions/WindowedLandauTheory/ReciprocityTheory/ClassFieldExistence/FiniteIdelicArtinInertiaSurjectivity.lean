import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ArtinResidueDegree
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteIdelicArtinLocalImages

/-! Surjectivity onto decomposition implies surjectivity from local
units onto inertia. Norms of an upper uniformizer remove the valuation
of a local preimage of an inertia element. -/

noncomputable section

open NumberField IsDedekindDomain WithZero
open scoped GlobalTheory.Reciprocity.AdicLiesOver IsMulCommutative Pointwise

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L]

local notation "G" => Gal(L/K)

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

theorem finiteIdelicArtin_range_localUnits_eq_inertia_of_range
    (f : IdeleGroup K →* G) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ a : Kˣ, f (diagonal K a) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (hsurj : (f.comp (finiteEmbedding v)).range = MulAction.stabilizer G w.asIdeal) :
    (unitsLevel v 0).map (f.comp (finiteEmbedding v)) = w.asIdeal.inertia G := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact finiteIdelicArtin_finiteEmbedding_mem_inertia f hf hd v w x hx
  intro σ hσ
  have hs : σ ∈ (f.comp (finiteEmbedding v)).range :=
    hsurj.symm ▸ Ideal.inertia_le_stabilizer w.asIdeal hσ
  obtain ⟨x, hx⟩ := hs
  let F := v.adicCompletion K
  let H := w.adicCompletion L
  let d := w.asIdeal.inertiaDeg (𝓞 K)
  have hI : f (finiteEmbedding v x) ∈ w.asIdeal.inertia G := hx.symm ▸ hσ
  obtain ⟨m, hm⟩ := inertiaDeg_dvd_ord_of_localArtin_mem_inertia f hf hd v w x hI
  obtain ⟨z, hz⟩ := exists_ord_eq_ite w
  let y := finiteProj w z
  have hy : - log (Valued.v (y : H)) = 1 := by
    change ord w z = 1
    exact (hz w).trans (if_pos rfl)
  let u := Units.map (Algebra.norm F) y
  have hu : -log (Valued.v (u : F)) = (d : ℤ) := by
    change -log (Valued.v (Algebra.norm F (y : H))) = _
    rw [valued_finiteCompletion_norm v w, log_pow, nsmul_eq_mul, neg_mul_eq_mul_neg, hy, mul_one]
  let w' : finitePlacesAbove L v := ⟨w, (mem_finitePlacesAbove L v w).mpr inferInstance⟩
  have huF : f (finiteEmbedding v u) = 1 :=
    finiteIdelicArtin_eq_one_on_single_local_norm f hf hd v w' y
  let x' := x / u ^ m
  have hvnz (b : Fˣ) : Valued.v b.val ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation F ℤᵐ⁰)).mpr b.ne_zero
  have hv : -(log (Valued.v (x' : F))) = 0 := by
    change -(log (Valued.v ((x / u ^ m : Fˣ) : F))) = 0
    have h := hm
    change -log (Valued.v (x : F)) = (d : ℤ) * m at h
    rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, map_div₀, map_zpow₀,
      log_div (hvnz x) (zpow_ne_zero _ (hvnz u)), log_zpow, zsmul_eq_mul]
    rw [show log (Valued.v (x : F)) = -((d : ℤ) * m) from neg_eq_iff_eq_neg.mp h,
      show log (Valued.v (u : F)) = -(d : ℤ) from neg_eq_iff_eq_neg.mp hu]
    change -(-((d : ℤ) * m) - m * -(d : ℤ)) = 0
    rw [mul_neg, mul_comm m (d : ℤ), sub_self, neg_zero]
  have h1 : Valued.v (x' : F) = 1 := by
    rw [← exp_log (hvnz x'), neg_eq_zero.mp hv, exp_zero]
  refine ⟨x', mem_unitsLevel.mpr ⟨h1, ?_⟩, ?_⟩
  · rw [Nat.cast_zero, neg_zero, exp_zero]
    exact Valued.v.map_sub_le h1.le (map_one Valued.v).le
  · change f (finiteEmbedding v (x / u ^ m)) = σ
    rw [map_div, map_zpow, map_div, map_zpow, huF, one_zpow, div_one]
    exact hx

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_range_localUnits_eq_inertia_of_range
