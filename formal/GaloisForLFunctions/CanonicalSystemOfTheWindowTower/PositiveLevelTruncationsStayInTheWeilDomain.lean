import GaloisForLFunctions.RHTower.CHMDSupportedApertureDomain
import GaloisForLFunctions.HTGeometry.AtomicJumpForm

/-!
# Positive-level tests in the completed Weil domain

Subtract a constant in the maximal inverse-Doob graph and take its positive part.
At a nonnegative level this operation preserves the original aperture. Its mixed
edge energy is nonnegative on every archimedean and prime edge, and dominates
the energy of the truncated vector.
-/

open MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open _root_.RHTower _root_.RHTower.CHMDDoobGraph _root_.RHTower.CHMDPolar
open HTGeometry

/-- The positive part above a level, formed in the full arithmetic jump graph. -/
def positiveLevelGraph (p : SourceGraph) (t : ℝ) : SourceGraph :=
  posGraph (p - constantLift t)

theorem positiveLevelGraph_source_ae (p : SourceGraph) (t : ℝ) :
    (positiveLevelGraph p t).val.fst =ᵐ[massMeasure]
      fun x => truncPos t (p.val.fst x) := by
  have hc : (constantLift t).val.fst =ᵐ[massMeasure] fun _ => t :=
    (memLp_const t : MemLp (fun _ : ℝ => t) 2 massMeasure).coeFn_toLp
  filter_upwards [posGraph_fst_ae (p - constantLift t),
    Lp.coeFn_sub p.val.fst (constantLift t).val.fst, hc] with x hp hs hc
  change (positiveLevelGraph p t).val.fst x = _ at hp
  rw [hp]
  change posFun ((p.val.fst - (constantLift t).val.fst) x) = _
  rw [hs, Pi.sub_apply, hc]
  rfl

theorem positiveLevelGraph_edge_ae (p : SourceGraph) (t : ℝ) :
    (positiveLevelGraph p t).val.snd =ᵐ[edgeMeasure]
      fun e => truncPos t (p.val.fst (left e)) - truncPos t (p.val.fst (right e)) := by
  filter_upwards [(positiveLevelGraph p t).property,
    nonsingular_left.ae (positiveLevelGraph_source_ae p t),
    nonsingular_right.ae (positiveLevelGraph_source_ae p t)] with e he hl hr
  rw [he, hl, hr]

/-- Level truncation is admissible on the same completed aperture, including its boundary. -/
theorem positiveLevelGraph_mem_aperture (a : SuzukiPositiveAperture)
    {p : SourceGraph} (hp : p ∈ apertureGraphCompletion a) {t : ℝ} (ht : 0 ≤ t) :
    positiveLevelGraph p t ∈ apertureGraphCompletion a := by
  apply (mem_apertureGraphCompletion_iff_supported a _).mpr
  apply (graphPhysicalSource_supported_iff a.1 _).mpr
  have hs := (graphPhysicalSource_supported_iff a.1 p).mp
    (physicalSource_supported_of_mem_apertureGraphCompletion a hp)
  filter_upwards [hs, positiveLevelGraph_source_ae p t] with x hx htrunc
  intro hnot
  rw [htrunc, hx hnot]
  simp only [truncPos, zero_sub, max_eq_right (neg_nonpos.mpr ht)]

/-- The actual mixed jump integrand dominates the squared truncated difference. -/
theorem positiveLevelGraph_edge_coercive_ae (p : SourceGraph) (t : ℝ) :
    ∀ᵐ e ∂edgeMeasure,
      (positiveLevelGraph p t).val.snd e ^ 2 ≤
        p.val.snd e * (positiveLevelGraph p t).val.snd e := by
  filter_upwards [p.property, positiveLevelGraph_edge_ae p t] with e hp hq
  rw [hp, hq]
  exact sub_mul_truncPos_sub_ge t _ _

theorem positiveLevelGraph_edge_nonneg_ae (p : SourceGraph) (t : ℝ) :
    ∀ᵐ e ∂edgeMeasure, 0 ≤ p.val.snd e * (positiveLevelGraph p t).val.snd e :=
  (positiveLevelGraph_edge_coercive_ae p t).mono fun _ he => (sq_nonneg _).trans he

/-- Truncation coercivity retains the complete prime-power edge measure. -/
theorem positiveLevelGraph_edge_inner_ge (p : SourceGraph) (t : ℝ) :
    ‖(positiveLevelGraph p t).val.snd‖ ^ 2 ≤
      inner ℝ p.val.snd (positiveLevelGraph p t).val.snd := by
  let r := p - constantLift t
  have he : r.val.snd = p.val.snd := by
    change p.val.snd - (constantLift t).val.snd = _
    rw [constantLift_edge, sub_zero]
  have hd := congrArg (fun q : SourceGraph => q.val.snd) (posGraph_sub_negGraph r)
  change (posGraph r).val.snd - (negGraph r).val.snd = r.val.snd at hd
  change ‖(posGraph r).val.snd‖ ^ 2 ≤ inner ℝ p.val.snd (posGraph r).val.snd
  rw [← he, ← hd, inner_sub_left, real_inner_self_eq_norm_sq]
  have hn := inner_posGraph_negGraph_snd_nonpos r
  rw [real_inner_comm] at hn
  linarith only [hn]

#print axioms positiveLevelGraph_mem_aperture
#print axioms positiveLevelGraph_edge_coercive_ae
#print axioms positiveLevelGraph_edge_inner_ge

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
