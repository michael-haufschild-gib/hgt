import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ChartLocalAlgebra
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedFixedPoints
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedFibreTrace

/-! The two pullbacks at a fixed point preserve all local values on
the normalized origin chart, including values of fractions. -/

noncomputable section

open GlobalTheory.PD GlobalTheory.SchemeCohomology

namespace GlobalTheory.WH

section Fraction

variable {k L : Type} [Field k] [Field L] [Algebra k L]
  {B : Subalgebra k L} {e : B →ₐ[k] k}

/-- Clearing a factor that is a unit at the point preserves the value
test for the remaining factor. -/
theorem val_of_val_mul {b z : L} {a c : k}
    (hb : Val B e b a) (ha : a ≠ 0) (hz : Val B e (b * z) (a * c)) :
    Val B e z c := by
  obtain ⟨hb, hbe⟩ := (val_iff_loc B e b a).mp hb
  obtain ⟨hz, hze⟩ := (val_iff_loc B e (b * z) (a * c)).mp hz
  let u : loc B e := ⟨b, hb⟩
  let v : loc B e := ⟨b * z, hz⟩
  have hunit : IsUnit u := isUnit_loc_of_eval_ne_zero B e u (hbe.symm ▸ ha)
  let w : loc B e := (↑hunit.unit⁻¹ : loc B e) * v
  have hmul : u * w = v := by
    calc
      u * w = (↑hunit.unit : loc B e) * w :=
        congrArg (fun r => r * w) hunit.unit_spec.symm
      _ = v := by
        change (↑hunit.unit : loc B e) * ((↑hunit.unit⁻¹ : loc B e) * v) = v
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hb0 : b ≠ 0 := (hunit.map (loc B e).val.toMonoidHom).ne_zero
  have hw : (w : L) = z := mul_left_cancel₀ hb0 (congrArg Subtype.val hmul)
  have hval : locEval B e w = c := by
    have heu : locEval B e u = a := hbe
    have hev : locEval B e v = a * c := hze
    have hprod := congrArg (locEval B e) hmul
    rw [map_mul, heu, hev] at hprod
    exact mul_left_cancel₀ ha hprod
  exact hw ▸ (val_iff_loc B e _ _).mpr ⟨w.property, hval⟩

end Fraction

variable {k F E L : Type} [Field k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra E L] [Algebra F L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F}

local notation "B" => rB k E x {0}
local notation "C" => rB k L x {0}
local notation "j₁" => IsScalarTower.toAlgHom k E L

/-- A fixed point of the correspondence over the origin determines a
common fibre evaluation for the two local pullbacks. -/
theorem exists_originFibrePoint_of_isFix (j₂ : E →ₐ[k] L)
    (f : OriginFibrePoint k L x) (hfix : IsFix C f.1 j₂ B) :
    ∃ e : OriginFibrePoint k E x,
      ∀ v c, Val B e.1 v c → Val C f.1 ((j₁) v) c ∧ Val C f.1 (j₂ v) c := by
  let g : B →ₐ[k] C := rBPullback x {0}
  have hg (a : B) : (g a : L) = (j₁) (a : E) := rBPullback_coe x {0} a
  let e₀ : B →ₐ[k] k := f.1.comp g
  have he (l : Fin d) : e₀ ⟨_, tco_mem k E x l⟩ = 0 := by
    have hh : g ⟨_, tco_mem k E x l⟩ = ⟨_, tco_mem k L x l⟩ :=
      rBPullback_originCoordinate x l
    change f.1 (g _) = 0
    rw [hh, f.2 l]
  refine ⟨⟨e₀, he⟩, ?_⟩
  have hregular (a : B) :
      Val C f.1 ((j₁) (a : E)) (e₀ a) ∧ Val C f.1 (j₂ (a : E)) (e₀ a) := by
    have hmem : (j₁) (a : E) ∈ C := hg a ▸ (g a).property
    refine ⟨hg a ▸ val_chartElement C f.1 (g a), ?_⟩
    have harg : (⟨algebraMap E L (a : E), hmem⟩ : C) = g a := Subtype.ext (hg a).symm
    have hf := hfix _ a.property hmem
    rw [harg] at hf
    exact hf
  intro v c hv
  obtain ⟨b, hb, hn, hb₀, hval⟩ := hv
  let bb : B := ⟨b, hb⟩
  let nn : B := ⟨b * v, hn⟩
  have hv₁ := (hregular nn).1
  have hv₂ := (hregular nn).2
  change Val C f.1 ((j₁) (b * v)) (e₀ nn) at hv₁
  change Val C f.1 (j₂ (b * v)) (e₀ nn) at hv₂
  rw [map_mul, show e₀ nn = e₀ bb * c from hval] at hv₁ hv₂
  exact ⟨val_of_val_mul (hregular bb).1 hb₀ hv₁,
    val_of_val_mul (hregular bb).2 hb₀ hv₂⟩

end GlobalTheory.WH
