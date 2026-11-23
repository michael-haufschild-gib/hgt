import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.LineLoss
import GaloisForLFunctions.RHTower.STCPrimeBoundaryTangentSpace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! # Operator and trace limits of admissible line omissions

Every excluded line can be approached by lines outside the range of critical
heat. Both the positive propagators and their fourth traces converge.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology ContinuousLinearMap InnerProductSpace

private theorem tendsto_positive_of_squares {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {l : Filter X} {F : X → H →L[ℂ] H} {B : H →L[ℂ] H}
    (hF : ∀ x, (F x).IsPositive) (hB : B.IsPositive)
    (h : Tendsto (fun x => F x^2) l (𝓝 (B^2))) : Tendsto F l (𝓝 B) := by
  have pos {T : H →L[ℂ] H} (hp : T.IsPositive) : 0 ≤ T^2 := by
    calc
      0 ≤ star T*T := star_mul_self_nonneg _
      _ = T^2 := by rw [hp.isSelfAdjoint.star_eq,pow_two]
  have hs := (CFC.continuousOn_sqrt (B^2) (pos hB)).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨h,Eventually.of_forall fun x => pos (hF x)⟩)
  rw [CFC.sqrt_sq B ((nonneg_iff_isPositive _).mpr hB)] at hs
  exact hs.congr fun x => CFC.sqrt_sq _ ((nonneg_iff_isPositive _).mpr (hF x))

/-- The positive root for a missing line depends continuously on its direction away from zero. -/
theorem continuousAt_omitted_root {v : Gas} (hv : v ≠ 0) :
    ContinuousAt (fun w => projected (omitLine w)) v := by
  apply tendsto_positive_of_squares (F := fun w : Gas => projected (omitLine w))
    (B := projected (omitLine v)) (fun _ => projected_positive _) (projected_positive _)
  change ContinuousAt (fun w : Gas => projected (omitLine w)^2) v
  simp_rw [line_square]
  apply continuousAt_const.sub
  have hw : ContinuousAt (fun w : Gas => ((‖w‖^2:ℝ):ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.norm.pow 2)
  have hi := hw.inv₀ (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr hv)))
  exact hi.smul (_root_.RHTower.continuous_rankOne_self.comp criticalOperator.continuous).continuousAt

/-- The zero direction is allowed, and a nonzero direction is allowed exactly outside the heat range. -/
theorem line_conserves_iff (v : Gas) :
    Conserving (projected (omitLine v)) ↔ (v ∈ LinearMap.range criticalOperator.toLinearMap → v = 0) := by
  let P := omitLine v
  have hk : P.val.toLinearMap.ker = ℂ ∙ v := by
    change (ℂ ∙ v)ᗮ.starProjection.toLinearMap.ker = _
    rw [Submodule.ker_starProjection,Submodule.orthogonal_orthogonal]
  rw [projected_conserves_iff,← Submodule.disjoint_span_singleton,← hk,LinearMap.disjoint_ker_iff_injOn]
  constructor
  · intro hi x ⟨a,ha⟩ y ⟨b,hb⟩ he
    subst x; subst y
    exact congrArg criticalOperator (hi he)
  · intro hi x y he
    exact critical_injective (hi ⟨x,rfl⟩ ⟨y,rfl⟩ he)

def readings : Set (GasOp × ℝ) := Set.range fun G : Propagator => (G.val,traceLoss G.val)

/-- Every hyperplane compression, together with its trace, lies in the closure of physical readings. -/
theorem line_reading_mem_closure (v : Gas) : (projected (omitLine v),lineLoss v) ∈ closure readings := by
  let R := LinearMap.range criticalOperator.toLinearMap
  by_cases hc : Conserving (projected (omitLine v))
  · apply subset_closure
    exact ⟨⟨_,projected_positive _,hc⟩,Prod.ext rfl (traceLoss_omitLine v)⟩
  have him : v ∈ R := by
    by_contra ho
    exact hc ((line_conserves_iff v).mpr (fun hv => (ho hv).elim))
  have hne : v ≠ 0 := fun hz => hc ((line_conserves_iff v).mpr (fun _ => hz))
  let s : HeatVectorDomain := ⟨1,by norm_num⟩
  have hout : packet s ∉ R := by
    change packet s ∉ Set.range criticalOperator
    rw [packet_in_range_iff]
    norm_num [s]
  let w (t : PacketScale) := v+(t.val:ℂ) • packet s
  have hw (t : PacketScale) : Conserving (projected (omitLine (w t))) := by
    apply (line_conserves_iff _).mpr
    intro hmem
    change v+(t.val:ℂ) • packet s ∈ R at hmem
    exact (hout ((R.smul_mem_iff (Complex.ofReal_ne_zero.mpr t.property.ne')).mp
      ((R.add_mem_iff_right him).mp hmem))).elim
  have hscale : Tendsto (fun t : PacketScale => (t.val:ℂ)) packetPole (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_comap.mono_right nhdsWithin_le_nhds : Tendsto Subtype.val packetPole (𝓝 (0:ℝ)))
  have hwv : Tendsto w packetPole (𝓝 v) := by
    simpa only [zero_smul,add_zero] using (tendsto_const_nhds (x := v)).add
      (hscale.smul (tendsto_const_nhds (x := packet s)))
  have hl := ((continuousAt_omitted_root hne).tendsto.comp hwv).prodMk_nhds
    ((continuousAt_lineLoss hne).tendsto.comp hwv)
  apply mem_closure_of_tendsto hl
  exact Eventually.of_forall fun t => ⟨⟨_,projected_positive _,hw t⟩,Prod.ext rfl (traceLoss_omitLine _)⟩

#print axioms continuousAt_omitted_root
#print axioms line_conserves_iff
#print axioms line_reading_mem_closure

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
