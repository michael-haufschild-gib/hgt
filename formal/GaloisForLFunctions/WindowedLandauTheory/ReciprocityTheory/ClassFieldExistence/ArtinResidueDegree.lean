import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldArithmeticFrobenius
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteIdelicArtinFrobeniusCoset

/-! Powers of arithmetic Frobenius lie in inertia exactly when their
exponent is divisible by the residue degree. -/

noncomputable section

open NumberField IsDedekindDomain WithZero GaloisForLFunctions
open GaloisForLFunctions.HTGeometry.ABHN
open scoped IsMulCommutative Pointwise

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L]

local notation "G" => Gal(L/K)

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

theorem arithFrobAt_zpow_mem_inertia_iff (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    {σ : G} (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) (i : ℤ) :
    σ ^ i ∈ w.asIdeal.inertia G ↔ (w.asIdeal.inertiaDeg (𝓞 K) : ℤ) ∣ i := by
  letI := v.isMaximal
  letI := w.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  letI := Ideal.Quotient.field w.asIdeal
  letI : Finite (𝓞 L ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  let D := MulAction.stabilizer G w.asIdeal
  let b : D := ⟨σ, hσ.mem_stabilizer⟩
  let r := Ideal.Quotient.stabilizerHom w.asIdeal v.asIdeal G
  let τ := finiteFieldArithmeticFrobenius (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal)
  have hr : r b = τ := by
    apply AlgEquiv.ext
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk w.asIdeal (σ • a) = τ (Ideal.Quotient.mk w.asIdeal a)
    rw [finiteFieldArithmeticFrobenius_apply, ← map_pow]
    apply Ideal.Quotient.eq.mpr
    have h := hσ a
    rwa [← Ideal.over_def w.asIdeal v.asIdeal] at h
  have ho : orderOf τ = w.asIdeal.inertiaDeg (𝓞 K) := by
    rw [orderOf_finiteFieldArithmeticFrobenius, Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal]
  have hk : r.ker.map (Subgroup.subtype D) = w.asIdeal.inertia G :=
    Ideal.Quotient.map_ker_stabilizer_subtype w.asIdeal v.asIdeal G
  have hmem : σ ^ i ∈ w.asIdeal.inertia G ↔ b ^ i ∈ r.ker := by
    rw [← hk]
    constructor
    · rintro ⟨z, hz, he⟩
      have he' : z = b ^ i := Subtype.ext he
      exact he' ▸ hz
    · intro h
      exact ⟨b ^ i, h, rfl⟩
  calc
    σ ^ i ∈ w.asIdeal.inertia G ↔ r (b ^ i) = 1 :=
      hmem.trans MonoidHom.mem_ker
    _ ↔ (w.asIdeal.inertiaDeg (𝓞 K) : ℤ) ∣ i := by
      rw [map_zpow, hr, ← orderOf_dvd_iff_zpow_eq_one, ho]

theorem inertiaDeg_dvd_ord_of_localArtin_mem_inertia
    (f : IdeleGroup K →* G) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ a : Kˣ, f (diagonal K a) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (x : (v.adicCompletion K)ˣ) (hx : f (finiteEmbedding v x) ∈ w.asIdeal.inertia G) :
    (w.asIdeal.inertiaDeg (𝓞 K) : ℤ) ∣ - log (Valued.v (x : v.adicCompletion K)) := by
  letI := w.isMaximal
  let σ := arithFrobAt (𝓞 K) G w.asIdeal
  let hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal := IsArithFrobAt.arithFrobAt (𝓞 K) G w.asIdeal
  apply (arithFrobAt_zpow_mem_inertia_iff v w hσ _).mp
  have he := finiteIdelicArtin_finiteEmbedding_div_frob_mem_inertia f hf hd v w σ hσ x
  have h := (w.asIdeal.inertia G).div_mem hx he
  rwa [div_div_cancel] at h

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.arithFrobAt_zpow_mem_inertia_iff
#print axioms GlobalTheory.Reciprocity.inertiaDeg_dvd_ord_of_localArtin_mem_inertia
