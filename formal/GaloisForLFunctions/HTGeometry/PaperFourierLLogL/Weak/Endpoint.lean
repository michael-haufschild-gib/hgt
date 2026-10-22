import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Weak.Signed

/-!
# Weak-type `L log L` bound for the symmetric Fourier maximal function

Rescales the modular-ball weak-type estimate to all of `L log L` via the Luxemburg norm
`‖f‖_Φ = inf {b > 0 | ∫ Φ(|f|/b) ≤ 1}` with `Φ(t) = t log(2 + t)`. The Luxemburg set of an `L log L`
function is nonempty, and dividing `f` by any admissible `b` places it in the modular unit ball,
where the level set of the maximal function scales accordingly.

## Main results

- `bill_renorm`: `∫ Φ(|f/b|) = ∫ Φ(|f|/b)`.
- `lux_exists`: every `f ∈ L log L` has a nonempty Luxemburg set.
- `consequence_maximal`: assuming `GoodBound`, there is `C > 0` such that for every `f ∈ L log L`
  and `w > 0`, `w · |{x | sup_N |S_N f(x)| > w}| ≤ C · ‖f‖_Φ`.

## Hypotheses

`consequence_maximal` is conditional on `GoodBound`, the Prop-valued good-set estimate for the
maximal partial-sum operator (proved elsewhere in the development as
`FourierLLogL.maximal_good_sets`). The other lemmas are unconditional.
-/

noncomputable section
open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

namespace FourierLLogL.Weak
open Real
open scoped Classical

/-- The rescaled function `f / b`. -/
def renorm (f : Torus → ℂ) (b : ℝ) := fun x => ((b⁻¹:ℝ):ℂ)*f x

lemma young_renorm (f : Torus → ℂ) (b : ℝ) (hh : 0 < b) :
    Young (renorm f b)=fun x => priceΦ (‖f x‖/b) := by
  funext x; unfold Young renorm
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.2 hh),←div_eq_inv_mul]
/-- For `b > 0`, the unit-scale modular of `f / b` equals the modular of `f` at scale `b`. -/
lemma bill_renorm (f : Torus → ℂ) (b : ℝ) (hh : 0 < b) :
    modBill (renorm f b) 1= modBill f b := by
  rw [mod_unit,show (fun x => Young (renorm f b) x)=_ from young_renorm _ _ hh]; rfl
/-- Every `L log L` function has some `b > 0` with `∫ Φ(|f|/b) ≤ 1`. -/
lemma lux_exists {f : Torus → ℂ} (h : MemLLogL f) : (luxSet f).Nonempty := by
  let T := modBill f 1; let b := max T 1
  have hb : 1 ≤ b := le_max_right _ _
  have hh : 0 < b := by linarith
  refine ⟨b, hh,?_⟩
  let g := renorm f b
  have HG : Integrable (Young g) law := (mem_dilate _ h).2
  rw [← bill_renorm f b hh,mod_unit]
  apply le_trans (b:=∫ x,b⁻¹*Young f x ∂law)
  · apply integral_mono HG ((show Integrable (Young f) law from h.2).const_mul _)
    rw [← show (fun x => Young (renorm f b) x)=Young g from rfl]
    intro x
    change Young (renorm f b) x ≤ _
    rw [young_renorm _ _ hh]
    let t := ‖f x‖
    have HT : 0 ≤ t := norm_nonneg _
    have hv : t/b ≤ t := div_le_self HT hb
    change (t/b)*log (2+t/b) ≤ b⁻¹*(t*log (2+t))
    rw [← mul_assoc,← div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply log_le_log (by positivity); linarith
  · rw [integral_const_mul]
    rw [show (∫ x, Young f x ∂law) = T from (mod_unit f).symm,←div_eq_inv_mul]
    exact (div_le_one hh).mpr (le_max_left _ _)

/-- Assuming `GoodBound`: weak-type `L log L` bound `w · |{M f > w}| ≤ C · ‖f‖_Φ` for the symmetric
Fourier maximal function, with `‖f‖_Φ` the Luxemburg norm for `Φ(t) = t log(2 + t)`. -/
lemma consequence_maximal (h : GoodBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Torus → ℂ), MemLLogL f →
      ∀ w : ℝ, 0 < w →
        w*circleMeasure.real (cloudSet f w) ≤ C*luxNorm f := by
  obtain ⟨C,hc,hF⟩ := circle_bill h
  refine ⟨C,hc,?_⟩
  intro f hf w hw
  let m := law.real (cloudSet f w)
  have H (b : ℝ) (hb : b∈luxSet f) :
      w*m ≤ C*b := by
    obtain ⟨hh,ht⟩ := hb
    let g := renorm f b
    have HE : inside g := ⟨mem_dilate _ hf,(bill_renorm f b hh).le.trans ht⟩
    have HP : cloudSet g (w/b)=cloudSet f w := by
      ext x
      rw [cloudy _ (by positivity) x,cloudy _ hw.le x]
      have Hz (i : ℕ) : ‖symmetricPartialSum g i x‖=‖symmetricPartialSum f i x‖/b := by
        unfold g renorm
        rw [symmetricPartialSum_const_mul,norm_mul, Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hh),← div_eq_inv_mul]
      simp_rw [Hz,div_lt_div_iff_of_pos_right hh]
    have HI := hF g HE (w/b) (div_pos hw hh)
    rw [HP,div_mul_eq_mul_div] at HI
    exact (div_le_iff₀ hh).1 HI
  have HV : w*m/C ≤ sInf (luxSet f) :=
    le_csInf (lux_exists hf) fun b hb => (div_le_iff₀ hc).mpr ((H b hb).trans (le_of_eq (mul_comm C b)))
  change w*m ≤ C*sInf (luxSet f)
  rw [mul_comm C]; exact (div_le_iff₀ hc).1 HV

end FourierLLogL.Weak

end GaloisForLFunctions.HTGeometry
