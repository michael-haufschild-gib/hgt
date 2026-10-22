import GaloisForLFunctions.RHTower.Suzuki.SuzukiFGammaBasis
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFGammaModelSpace

noncomputable section

/-!
# The de Branges vectors are entire

`E F_γ` is entire, and it lies in the de Branges space `H(E)`.

The point is that no boundary-gluing argument is needed: `F_γ` is a divided slope of `A/E`, so
`E F_γ` is the divided slope of `A` itself, and the divided slope of an entire function is entire.
Off the zeros of `E` the two descriptions agree, and at a zero of `E` the entire one is the correct
value.

The two Hardy conditions defining `H(E)` are exactly the two conditions defining the model space for
`F_γ`: the first quotient is `F_γ` almost everywhere, and the second is `Θ conj(F_γ) = -F_γ`.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The de Branges vector `E F_γ`, written directly as an entire function. -/
def suzukiDeBrangesVector (γ : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  ((Real.sqrt ((m : ℝ) / Real.pi) : ℝ) : ℂ) * (I * dslope XiC ((γ : ℝ) : ℂ) z)

/-- **The de Branges vectors are entire.**  The divided slope of an entire function is entire. -/
theorem differentiable_suzukiDeBrangesVector (γ : ℝ) (m : ℕ) :
    Differentiable ℂ (suzukiDeBrangesVector γ m) := by
  have hd : Differentiable ℂ (dslope XiC ((γ : ℝ) : ℂ)) := by
    rw [← differentiableOn_univ]
    refine (Complex.differentiableOn_dslope (by simp)).mpr ?_
    exact XiC_differentiable.differentiableOn
  intro z
  exact ((hd z).const_mul I).const_mul _

/-- Off the zeros of `E` the de Branges vector is `E F_γ`. -/
theorem suzukiDeBrangesVector_eq {γ : ℝ} {m : ℕ} (hγ : XiC ((γ : ℝ) : ℂ) = 0) {z : ℂ}
    (hE : xiHedenmalmDeBrangesE z ≠ 0) :
    suzukiDeBrangesVector γ m z = xiHedenmalmDeBrangesE z * suzukiFGammaFun γ m z := by
  by_cases hz : z = ((γ : ℝ) : ℂ)
  · subst hz
    have hA : HasDerivAt XiC (deriv XiC ((γ : ℝ) : ℂ)) ((γ : ℝ) : ℂ) :=
      (XiC_differentiable _).hasDerivAt
    have hEd : HasDerivAt xiHedenmalmDeBrangesE
        (deriv xiHedenmalmDeBrangesE ((γ : ℝ) : ℂ)) ((γ : ℝ) : ℂ) :=
      (differentiable_xiHedenmalmDeBrangesE _).hasDerivAt
    have hdiv := hA.div hEd hE
    have h1 : HasDerivAt suzukiHalfInner
        ((deriv XiC ((γ : ℝ) : ℂ) * xiHedenmalmDeBrangesE ((γ : ℝ) : ℂ)
          - XiC ((γ : ℝ) : ℂ) * deriv xiHedenmalmDeBrangesE ((γ : ℝ) : ℂ))
          / (xiHedenmalmDeBrangesE ((γ : ℝ) : ℂ)) ^ (2 : ℕ)) ((γ : ℝ) : ℂ) := hdiv
    have hval : deriv suzukiHalfInner ((γ : ℝ) : ℂ)
        = deriv XiC ((γ : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((γ : ℝ) : ℂ) := by
      rw [h1.deriv, hγ]
      field_simp
      ring
    rw [suzukiDeBrangesVector, suzukiFGammaFun, dslope_same, dslope_same, hval]
    field_simp
  · rw [suzukiDeBrangesVector, suzukiFGammaFun,
      dslope_of_ne _ hz, dslope_of_ne _ hz, slope_def_field, slope_def_field,
      hγ, suzukiHalfInner_eq_zero_of_XiC_zero hγ]
    rw [suzukiHalfInner]
    field_simp
    ring

/-! ## `E F_γ` belongs to the de Branges space -/

theorem coeFn_suzukiDeBrangesVector_div {γ : ℝ} {m : ℕ}
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    (fun x : ℝ =>
        suzukiDeBrangesVector γ m ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
      =ᵐ[volume] fun x : ℝ => suzukiFGammaFun γ m ((x : ℝ) : ℂ) := by
  filter_upwards [ae_xiHedenmalmDeBrangesE_ofReal_ne_zero] with x hE
  rw [suzukiDeBrangesVector_eq hγ hE, mul_comm, mul_div_assoc, div_self hE, mul_one]

theorem memLp_suzukiDeBrangesVector_div (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞))
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    MemLp (fun x : ℝ =>
      suzukiDeBrangesVector γ m ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
      2 (volume : Measure ℝ) :=
  (memLp_congr_ae (coeFn_suzukiDeBrangesVector_div hγ)).mpr
    (memLp_suzukiFGammaFun hRH hm hord hγ)

theorem coeFn_suzukiDeBrangesVector_sharp_div {γ : ℝ} {m : ℕ}
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    (fun x : ℝ => (starRingEnd ℂ) (suzukiDeBrangesVector γ m ((x : ℝ) : ℂ))
        / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ))
      =ᵐ[volume] fun x : ℝ => -suzukiFGammaFun γ m ((x : ℝ) : ℂ) := by
  have hnull : volume ({γ} : Set ℝ) = 0 := by simp
  filter_upwards [ae_xiHedenmalmDeBrangesE_ofReal_ne_zero,
    MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hE hxγ
  have hx : x ≠ γ := fun h => hxγ (by simp [h])
  have hsharp : (starRingEnd ℂ) (suzukiDeBrangesVector γ m ((x : ℝ) : ℂ))
      = xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ)
        * (starRingEnd ℂ) (suzukiFGammaFun γ m ((x : ℝ) : ℂ)) := by
    rw [suzukiDeBrangesVector_eq hγ hE, map_mul,
      xiHedenmalmDeBrangesESharp_ofReal_eq_conj]
  have hsym : suzukiThetaSymbol x
      = xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ)
        / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) := by
    rw [suzukiThetaSymbol, if_neg hE]
  have hkey := suzukiThetaSymbol_mul_conj_suzukiFGammaFun m hγ hx hE
  rw [hsym] at hkey
  rw [hsharp, ← hkey]
  field_simp

theorem memLp_suzukiDeBrangesVector_sharp_div (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞))
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    MemLp (fun x : ℝ => (starRingEnd ℂ) (suzukiDeBrangesVector γ m ((x : ℝ) : ℂ))
      / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ) :=
  (memLp_congr_ae (coeFn_suzukiDeBrangesVector_sharp_div hγ)).mpr
    ((memLp_suzukiFGammaFun hRH hm hord hγ).neg)

/-- **`E F_γ` lies in the de Branges space `H(E)`.**  The de Branges vectors are entire, and the
two Hardy conditions are those of `F_γ` in the model space. -/
theorem memDeBranges_suzukiDeBrangesVector (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞))
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    MemDeBranges (suzukiDeBrangesVector γ m) := by
  refine (memDeBranges_iff_mem_suzukiModelSpace (differentiable_suzukiDeBrangesVector γ m)
    (memLp_suzukiDeBrangesVector_div hRH hm hord hγ)
    (memLp_suzukiDeBrangesVector_sharp_div hRH hm hord hγ)).mpr ?_
  have heq : (memLp_suzukiDeBrangesVector_div hRH hm hord hγ).toLp _
      = suzukiFGammaLp hRH hm hord hγ := by
    refine MeasureTheory.Lp.ext ?_
    refine ((memLp_suzukiDeBrangesVector_div hRH hm hord hγ).coeFn_toLp).trans ?_
    refine (coeFn_suzukiDeBrangesVector_div hγ).trans ?_
    exact (coeFn_suzukiFGammaLp hRH hm hord hγ).symm
  rw [heq]
  exact suzukiFGammaLp_mem_suzukiModelSpace hRH hm hord hγ


end RHTower
