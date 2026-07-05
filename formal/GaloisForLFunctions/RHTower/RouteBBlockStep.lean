/-
The block anti-concentration step of the hierarchical small-ball law for the
Steinhaus field.  A prime-supported block sum, conditioned on all other phases,
is anti-concentrated at the four-phase caustic rate: the Steinhaus small-ball
probability of `w + Σ_{n ∈ s} aₙ Xₙ` is bounded, uniformly in the conditioning
value `w`, by `(2π)⁻⁴` times the four-phase constant carried by any four
distinguished dominant prime coordinates.

The four dominant phases are integrated out first (the center-uniform four-phase
law after peeling and rescaling), and the remaining coordinates pass their
constant through a probability measure.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBProdFubini
import GaloisForLFunctions.RHTower.RouteBFourPhaseUniform

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- The explicit four-phase small-ball constant: the dyadic-shell term (scaling
`J·r²`), the two core terms, and the mid term, in the caustic coordinates. -/
noncomputable def fourPhaseConst (A B C D : ℂ) (r σ0 sstar : ℝ) (J : ℕ) : ENNReal :=
  ENNReal.ofReal ((2 * Real.pi) ^ 3)
      * ENNReal.ofReal (8 * Real.pi * sstar / ‖D‖)
    + ENNReal.ofReal (2 * (Real.pi * r / ‖A‖)
        * ((J : ℝ) * (8 * Real.pi ^ 2
          * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
          * Real.sqrt (2 / (causticKappa ‖A‖ ‖B‖ * ‖C‖)))
        + 2 * ((2 * Real.pi * Real.sqrt (2 * (r * (2 * ‖A‖ + r)
            / ((‖A‖ - ‖B‖) / 2 * ‖B‖))))
          * (2 * Real.pi * Real.sqrt ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r))
            / ‖C‖))))
        / Real.sqrt sstar)
      * ENNReal.ofReal (2 * Real.pi)
    + ENNReal.ofReal (2 * (Real.pi * r / ‖A‖)
        * ((J : ℝ) * (8 * Real.pi ^ 2
          * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
          * Real.sqrt 2)
        + 2 * Real.pi * (2 * Real.pi
          * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
          / Real.sqrt (min (((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3
              * causticKappa ‖A‖ ‖B‖ / 2) (1 / 2)))))
      * ENNReal.ofReal (2 * Real.pi)

/-- The four-fold iterated angle integral of the sublevel indicator, at
any center `w`, is at most the explicit four-phase constant. -/
theorem four_phase_nested_uniform {A B C D w : ℂ} {r σ0 sstar : ℝ}
    {J : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hρB : ‖B‖ < ‖A‖) (hr0 : 0 < r) (hr2 : 2 * r ≤ ‖A‖ - ‖B‖)
    (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3)
    (hJ : ((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3 < 2 ^ J * σ0)
    (hHσ0 : 2 * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) * ‖B‖))
        ≤ σ0 * causticKappa ‖A‖ ‖B‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖D‖) :
    ∫⁻ θD in Set.Icc (0 : ℝ) (2 * Real.pi),
        ∫⁻ θC in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫⁻ θB in Set.Icc (0 : ℝ) (2 * Real.pi),
            ∫⁻ θA in Set.Icc (0 : ℝ) (2 * Real.pi),
              {θ' : ℝ | ‖w + D * Complex.exp ((θD : ℂ) * Complex.I)
                  + C * Complex.exp ((θC : ℂ) * Complex.I)
                  + B * Complex.exp ((θB : ℂ) * Complex.I)
                  + A * Complex.exp ((θ' : ℂ) * Complex.I)‖ ≤ r}.indicator
                (fun _ => (1 : ENNReal)) θA
      ≤ fourPhaseConst A B C D r σ0 sstar J := by
  exact le_trans (le_of_eq (four_phase_prod_eq_nested A B C D w r).symm)
    (four_phase_sublevel_uniform hA hB hC hD hρB hr0 hr2 hσ0 hσ0G hJ hHσ0
      hss hss2)

end Sublevel
end RHTower

namespace RHTower
namespace SteinhausModel

open MeasureTheory Finset

/-- The unit-interval phase `exp(2πi x)`; the value of a prime Steinhaus
character before the angle rescale. -/
noncomputable def unitPhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((x : ℝ) : ℂ))

/-- Updating four distinguished block coordinates splits the phase sum into
the four fresh phases plus the frozen remainder over the other coordinates. -/
theorem sum_phase_update4 (s : Finset ℕ) (a : ℕ → ℝ) (y : ↥s → ℝ)
    (q1 q2 q3 q4 : ↥s) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h14 : q1 ≠ q4)
    (h23 : q2 ≠ q3) (h24 : q2 ≠ q4) (h34 : q3 ≠ q4) (x1 x2 x3 x4 : ℝ) :
    ∑ p ∈ s.attach, (a ↑p : ℂ) *
        unitPhase (Function.update (Function.update (Function.update
              (Function.update y q1 x1) q2 x2) q3 x3) q4 x4 p)
      = (a ↑q1 : ℂ) * unitPhase x1 + (a ↑q2 : ℂ) * unitPhase x2
        + (a ↑q3 : ℂ) * unitPhase x3 + (a ↑q4 : ℂ) * unitPhase x4
        + ∑ p ∈ (s.attach \ {q1, q2, q3, q4}), (a ↑p : ℂ) * unitPhase (y p) := by
  have peel : ∀ (S : Finset ↥s) (z : ↥s → ℝ) (q : ↥s) (v : ℝ), q ∈ S →
      ∑ p ∈ S, (a ↑p : ℂ) * unitPhase (Function.update z q v p)
        = (a ↑q : ℂ) * unitPhase v + ∑ p ∈ (S \ {q}), (a ↑p : ℂ) * unitPhase (z p) := by
    intro S z q v hq
    have comm : (fun p : ↥s => (a ↑p : ℂ) * unitPhase (Function.update z q v p))
        = Function.update (fun p : ↥s => (a ↑p : ℂ) * unitPhase (z p)) q
            ((a ↑q : ℂ) * unitPhase v) := by
      funext p
      by_cases h : p = q
      · subst h; simp [Function.update_self]
      · simp [Function.update_of_ne h]
    rw [Finset.sum_congr rfl (fun p _ => congrFun comm p), sum_update_of_mem hq]
  have hq4 : q4 ∈ s.attach := mem_attach s q4
  have hq3 : q3 ∈ (s.attach \ {q4}) :=
    Finset.mem_sdiff.mpr ⟨mem_attach s q3, by simp [h34]⟩
  have hq2 : q2 ∈ ((s.attach \ {q4}) \ {q3}) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨mem_attach s q2, by simp [h24]⟩, by simp [h23]⟩
  have hq1 : q1 ∈ (((s.attach \ {q4}) \ {q3}) \ {q2}) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr
      ⟨mem_attach s q1, by simp [h14]⟩, by simp [h13]⟩, by simp [h12]⟩
  rw [peel _ _ q4 x4 hq4, peel _ _ q3 x3 hq3, peel _ _ q2 x2 hq2, peel _ _ q1 x1 hq1]
  have hsdiff : (((s.attach \ {q4}) \ {q3}) \ {q2}) \ {q1}
      = s.attach \ {q1, q2, q3, q4} := by
    ext p; simp only [mem_sdiff, mem_insert, mem_singleton]; tauto
  rw [hsdiff]; ring

/-- Rescaling four unit-interval phases to the angle interval `[0, 2π]`
carries a Jacobian `(2π)⁻¹` per coordinate. -/
theorem rescale4 (G : ℝ → ℝ → ℝ → ℝ → ENNReal)
    (hG : Measurable fun q : ℝ × ℝ × ℝ × ℝ => G q.1 q.2.1 q.2.2.1 q.2.2.2) :
    ∫⁻ x1 in Set.Icc (0:ℝ) 1, ∫⁻ x2 in Set.Icc (0:ℝ) 1,
        ∫⁻ x3 in Set.Icc (0:ℝ) 1, ∫⁻ x4 in Set.Icc (0:ℝ) 1,
          G (2 * Real.pi * x1) (2 * Real.pi * x2) (2 * Real.pi * x3) (2 * Real.pi * x4)
      = ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 *
          ∫⁻ θ1 in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θ2 in Set.Icc (0:ℝ) (2*Real.pi),
            ∫⁻ θ3 in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi),
              G θ1 θ2 θ3 θ4 := by
  set c := ENNReal.ofReal (2 * Real.pi)⁻¹ with hc
  have hcne : c ≠ ⊤ := by rw [hc]; simp
  have e4 : ∀ x1 x2 x3 : ℝ,
      (∫⁻ x4 in Set.Icc (0:ℝ) 1,
          G (2*Real.pi*x1) (2*Real.pi*x2) (2*Real.pi*x3) (2*Real.pi*x4))
        = c * ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi),
            G (2*Real.pi*x1) (2*Real.pi*x2) (2*Real.pi*x3) θ4 :=
    fun x1 x2 x3 => lintegral_two_pi_rescale (by fun_prop)
  have e3 : ∀ x1 x2 : ℝ,
      (∫⁻ x3 in Set.Icc (0:ℝ) 1, ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi),
          G (2*Real.pi*x1) (2*Real.pi*x2) (2*Real.pi*x3) θ4)
        = c * ∫⁻ θ3 in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi),
            G (2*Real.pi*x1) (2*Real.pi*x2) θ3 θ4 :=
    fun x1 x2 => lintegral_two_pi_rescale
      (g := fun θ3 => ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi),
        G (2*Real.pi*x1) (2*Real.pi*x2) θ3 θ4) (by fun_prop)
  have e2 : ∀ x1 : ℝ,
      (∫⁻ x2 in Set.Icc (0:ℝ) 1, ∫⁻ θ3 in Set.Icc (0:ℝ) (2*Real.pi),
          ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi), G (2*Real.pi*x1) (2*Real.pi*x2) θ3 θ4)
        = c * ∫⁻ θ2 in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θ3 in Set.Icc (0:ℝ) (2*Real.pi),
            ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi), G (2*Real.pi*x1) θ2 θ3 θ4 :=
    fun x1 => lintegral_two_pi_rescale
      (g := fun θ2 => ∫⁻ θ3 in Set.Icc (0:ℝ) (2*Real.pi),
        ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi), G (2*Real.pi*x1) θ2 θ3 θ4) (by fun_prop)
  have e1 :
      (∫⁻ x1 in Set.Icc (0:ℝ) 1, ∫⁻ θ2 in Set.Icc (0:ℝ) (2*Real.pi),
          ∫⁻ θ3 in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi),
            G (2*Real.pi*x1) θ2 θ3 θ4)
        = c * ∫⁻ θ1 in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θ2 in Set.Icc (0:ℝ) (2*Real.pi),
            ∫⁻ θ3 in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi),
              G θ1 θ2 θ3 θ4 :=
    lintegral_two_pi_rescale
      (g := fun θ1 => ∫⁻ θ2 in Set.Icc (0:ℝ) (2*Real.pi),
        ∫⁻ θ3 in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θ4 in Set.Icc (0:ℝ) (2*Real.pi),
          G θ1 θ2 θ3 θ4) (by fun_prop)
  simp_rw [e4]
  simp_rw [lintegral_const_mul' c _ hcne]
  simp_rw [e3]
  simp_rw [lintegral_const_mul' c _ hcne]
  simp_rw [e2]
  simp_rw [lintegral_const_mul' c _ hcne]
  rw [e1]
  ring

/-- Peeling four distinguished coordinates of an lmarginal into four iterated
single integrals. -/
theorem peel4 {ι : Type} [DecidableEq ι] (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : (ι → ℝ) → ENNReal) (hf : Measurable f)
    (q1 q2 q3 q4 : ι) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h14 : q1 ≠ q4)
    (h23 : q2 ≠ q3) (h24 : q2 ≠ q4) (h34 : q3 ≠ q4) (y : ι → ℝ) :
    (∫⋯∫⁻_{q1, q2, q3, q4}, f ∂μ) y
      = ∫⁻ x1, ∫⁻ x2, ∫⁻ x3, ∫⁻ x4,
          f (Function.update (Function.update (Function.update
              (Function.update y q1 x1) q2 x2) q3 x3) q4 x4)
          ∂μ q4 ∂μ q3 ∂μ q2 ∂μ q1 := by
  rw [show ({q1, q2, q3, q4} : Finset ι) = insert q1 ({q2, q3, q4} : Finset ι) from rfl,
    lmarginal_insert f hf (by simp [h12, h13, h14])]
  refine lintegral_congr fun x1 => ?_
  rw [show ({q2, q3, q4} : Finset ι) = insert q2 ({q3, q4} : Finset ι) from rfl,
    lmarginal_insert f hf (by simp [h23, h24])]
  refine lintegral_congr fun x2 => ?_
  rw [show ({q3, q4} : Finset ι) = insert q3 ({q4} : Finset ι) from rfl,
    lmarginal_insert f hf (by simp [h34])]
  refine lintegral_congr fun x3 => ?_
  rw [show ({q4} : Finset ι) = insert q4 (∅ : Finset ι) from rfl,
    lmarginal_insert f hf (by simp)]
  refine lintegral_congr fun x4 => ?_
  rw [lmarginal_empty]

open RHTower.Sublevel

/-- The four-coordinate marginal of the block small-ball indicator, at any
conditioning `y`, is bounded by `(2π)⁻⁴ M` whenever the four dominant phases
satisfy the uniform four-phase bound `M` at every center. -/
theorem inner_block_le (s : Finset ℕ) (a : ℕ → ℝ) (w : ℂ) (t : ℝ)
    (q1 q2 q3 q4 : ↥s) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h14 : q1 ≠ q4)
    (h23 : q2 ≠ q3) (h24 : q2 ≠ q4) (h34 : q3 ≠ q4) (M : ENNReal)
    (hM : ∀ V : ℂ,
      (∫⁻ θD in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θC in Set.Icc (0:ℝ) (2*Real.pi),
        ∫⁻ θB in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θA in Set.Icc (0:ℝ) (2*Real.pi),
          {θ' : ℝ | ‖V + (a ↑q1:ℂ) * Complex.exp ((θD:ℂ)*Complex.I)
              + (a ↑q2:ℂ) * Complex.exp ((θC:ℂ)*Complex.I)
              + (a ↑q3:ℂ) * Complex.exp ((θB:ℂ)*Complex.I)
              + (a ↑q4:ℂ) * Complex.exp ((θ':ℂ)*Complex.I)‖ ≤ t}.indicator
            (fun _ => (1:ENNReal)) θA) ≤ M)
    (y : ↥s → ℝ) :
    (∫⋯∫⁻_{q1, q2, q3, q4},
        ({x : ↥s → ℝ | ‖w + ∑ p ∈ s.attach, (a ↑p:ℂ) * unitPhase (x p)‖ ≤ t}.indicator
          (fun _ => (1:ENNReal)))
        ∂(fun _ : ↥s => volume.restrict (Set.Icc (0:ℝ) 1))) y
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
  set μ : ↥s → Measure ℝ := fun _ => volume.restrict (Set.Icc (0:ℝ) 1) with hμ
  set V : ℂ := w + ∑ p ∈ (s.attach \ {q1, q2, q3, q4}), (a ↑p:ℂ) * unitPhase (y p) with hV
  set Gfun : ℝ → ℝ → ℝ → ℝ → ENNReal := fun θ1 θ2 θ3 θ4 =>
    {z : ℂ | ‖z‖ ≤ t}.indicator (fun _ => (1:ENNReal))
      (V + (a ↑q1:ℂ) * Complex.exp ((θ1:ℂ)*Complex.I)
        + (a ↑q2:ℂ) * Complex.exp ((θ2:ℂ)*Complex.I)
        + (a ↑q3:ℂ) * Complex.exp ((θ3:ℂ)*Complex.I)
        + (a ↑q4:ℂ) * Complex.exp ((θ4:ℂ)*Complex.I)) with hGfun
  have hSm : MeasurableSet {z : ℂ | ‖z‖ ≤ t} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hE'm : MeasurableSet {x : ↥s → ℝ | ‖w + ∑ p ∈ s.attach, (a ↑p:ℂ) * unitPhase (x p)‖ ≤ t} := by
    apply IsClosed.measurableSet
    apply isClosed_le _ continuous_const
    apply Continuous.norm
    apply Continuous.add continuous_const
    apply continuous_finsetSum
    intro p _
    exact continuous_const.mul (by unfold unitPhase; fun_prop)
  have hf : Measurable ({x : ↥s → ℝ | ‖w + ∑ p ∈ s.attach, (a ↑p:ℂ) * unitPhase (x p)‖ ≤ t}.indicator
      (fun _ => (1:ENNReal))) := measurable_const.indicator hE'm
  rw [peel4 μ _ hf q1 q2 q3 q4 h12 h13 h14 h23 h24 h34 y]
  have he : ∀ x : ℝ, unitPhase x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    intro x; unfold unitPhase; congr 1; push_cast; ring
  have hpt : ∀ x1 x2 x3 x4 : ℝ,
      ({x : ↥s → ℝ | ‖w + ∑ p ∈ s.attach, (a ↑p:ℂ) * unitPhase (x p)‖ ≤ t}.indicator
          (fun _ => (1:ENNReal)))
        (Function.update (Function.update (Function.update
          (Function.update y q1 x1) q2 x2) q3 x3) q4 x4)
      = Gfun (2*Real.pi*x1) (2*Real.pi*x2) (2*Real.pi*x3) (2*Real.pi*x4) := by
    intro x1 x2 x3 x4
    have hval : w + ∑ p ∈ s.attach, (a ↑p:ℂ) *
          unitPhase (Function.update (Function.update (Function.update
              (Function.update y q1 x1) q2 x2) q3 x3) q4 x4 p)
        = V + (a ↑q1:ℂ) * Complex.exp (((2*Real.pi*x1:ℝ):ℂ)*Complex.I)
            + (a ↑q2:ℂ) * Complex.exp (((2*Real.pi*x2:ℝ):ℂ)*Complex.I)
            + (a ↑q3:ℂ) * Complex.exp (((2*Real.pi*x3:ℝ):ℂ)*Complex.I)
            + (a ↑q4:ℂ) * Complex.exp (((2*Real.pi*x4:ℝ):ℂ)*Complex.I) := by
      rw [sum_phase_update4 s a y q1 q2 q3 q4 h12 h13 h14 h23 h24 h34 x1 x2 x3 x4, hV]
      simp only [he]; ring
    simp only [hGfun, Set.indicator_apply, Set.mem_setOf_eq, hval]
  simp_rw [hμ, hpt]
  rw [rescale4 Gfun (by
    simp only [hGfun]
    exact (measurable_const.indicator hSm).comp (by fun_prop))]
  refine mul_le_mul_right ?_ _
  refine le_trans (le_of_eq ?_) (hM V)
  simp only [hGfun, Set.indicator_apply, Set.mem_setOf_eq]

/-- The finite-product block small-ball measure is bounded by `(2π)⁻⁴ M`,
uniformly over the four dominant phases: the extra coordinates are integrated
against a probability measure and pass the constant through. -/
theorem block_pi_le (s : Finset ℕ) (a : ℕ → ℝ) (w : ℂ) (t : ℝ)
    (q1 q2 q3 q4 : ↥s) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h14 : q1 ≠ q4)
    (h23 : q2 ≠ q3) (h24 : q2 ≠ q4) (h34 : q3 ≠ q4) (M : ENNReal)
    (hM : ∀ V : ℂ,
      (∫⁻ θD in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θC in Set.Icc (0:ℝ) (2*Real.pi),
        ∫⁻ θB in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θA in Set.Icc (0:ℝ) (2*Real.pi),
          {θ' : ℝ | ‖V + (a ↑q1:ℂ) * Complex.exp ((θD:ℂ)*Complex.I)
              + (a ↑q2:ℂ) * Complex.exp ((θC:ℂ)*Complex.I)
              + (a ↑q3:ℂ) * Complex.exp ((θB:ℂ)*Complex.I)
              + (a ↑q4:ℂ) * Complex.exp ((θ':ℂ)*Complex.I)‖ ≤ t}.indicator
            (fun _ => (1:ENNReal)) θA) ≤ M) :
    (Measure.pi (fun _ : ↥s => volume.restrict (Set.Icc (0:ℝ) 1)))
        {x : ↥s → ℝ | ‖w + ∑ p ∈ s.attach, (a ↑p:ℂ) * unitPhase (x p)‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
  haveI : ∀ i : ↥s, IsProbabilityMeasure ((fun _ : ↥s => volume.restrict (Set.Icc (0:ℝ) 1)) i) :=
    fun _ => ⟨by simp⟩
  set μ : ↥s → Measure ℝ := fun _ => volume.restrict (Set.Icc (0:ℝ) 1) with hμ
  set E' := {x : ↥s → ℝ | ‖w + ∑ p ∈ s.attach, (a ↑p:ℂ) * unitPhase (x p)‖ ≤ t} with hE'
  have hE'm : MeasurableSet E' := by
    apply IsClosed.measurableSet
    apply isClosed_le _ continuous_const
    apply Continuous.norm
    apply Continuous.add continuous_const
    apply continuous_finsetSum
    intro p _
    exact continuous_const.mul (by unfold unitPhase; fun_prop)
  have hfm : Measurable (E'.indicator (fun _ => (1:ENNReal))) := measurable_const.indicator hE'm
  have hpiE : (Measure.pi μ) E' = ∫⁻ x, E'.indicator (fun _ => (1:ENNReal)) x ∂(Measure.pi μ) := by
    rw [lintegral_indicator hE'm, setLIntegral_one]
  rw [hpiE, lintegral_eq_lmarginal_univ (μ := μ) (fun _ => (0:ℝ))]
  rw [show (Finset.univ : Finset ↥s)
        = (Finset.univ \ {q1, q2, q3, q4}) ∪ {q1, q2, q3, q4} from
      (Finset.sdiff_union_of_subset (Finset.subset_univ _)).symm]
  rw [lmarginal_union μ _ hfm Finset.sdiff_disjoint]
  have hbound : (fun z => (∫⋯∫⁻_{q1, q2, q3, q4}, E'.indicator (fun _ => (1:ENNReal)) ∂μ) z)
      ≤ fun _ => ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
    intro z
    exact inner_block_le s a w t q1 q2 q3 q4 h12 h13 h14 h23 h24 h34 M hM z
  refine le_trans (lmarginal_mono hbound _) (le_of_eq ?_)
  rw [lmarginal]
  simp only [lintegral_const]
  rw [measure_univ, mul_one]

/-- **The block anti-concentration step.**  For a prime-supported block `s`
with four distinguished dominant primes `p₁, p₂, p₃, p₄`, the Steinhaus
small-ball probability of `w + Σ_{n ∈ s} aₙ Xₙ` is at most `(2π)⁻⁴ M` whenever
those four coordinates satisfy the uniform four-phase bound `M` at every center
`V` — uniformly in the conditioning value `w`. -/
theorem block_smallball_condition
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (a : ℕ → ℝ) (w : ℂ) (t : ℝ)
    (p1 p2 p3 p4 : ℕ) (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (hp3 : p3 ∈ s) (hp4 : p4 ∈ s)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4) (M : ENNReal)
    (hM : ∀ V : ℂ,
      (∫⁻ θD in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θC in Set.Icc (0:ℝ) (2*Real.pi),
        ∫⁻ θB in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θA in Set.Icc (0:ℝ) (2*Real.pi),
          {θ' : ℝ | ‖V + (a p1:ℂ) * Complex.exp ((θD:ℂ)*Complex.I)
              + (a p2:ℂ) * Complex.exp ((θC:ℂ)*Complex.I)
              + (a p3:ℂ) * Complex.exp ((θB:ℂ)*Complex.I)
              + (a p4:ℂ) * Complex.exp ((θ':ℂ)*Complex.I)‖ ≤ t}.indicator
            (fun _ => (1:ENNReal)) θA) ≤ M) :
    steinhausMeasure {ω : Omega | ‖w + ∑ n ∈ s, (a n:ℂ) * X n ω‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
  rw [block_marginal hs a w t]
  exact block_pi_le s a w t ⟨p1, hp1⟩ ⟨p2, hp2⟩ ⟨p3, hp3⟩ ⟨p4, hp4⟩
    (fun h => h12 (Subtype.ext_iff.mp h)) (fun h => h13 (Subtype.ext_iff.mp h))
    (fun h => h14 (Subtype.ext_iff.mp h)) (fun h => h23 (Subtype.ext_iff.mp h))
    (fun h => h24 (Subtype.ext_iff.mp h)) (fun h => h34 (Subtype.ext_iff.mp h)) M hM

/-- **The four-phase Steinhaus block small-ball law.**  For a prime-supported
block with four dominant primes in strict caustic position (`|a p₄| > |a p₃|`,
the radius/margin windows, and split parameters), the Steinhaus small-ball
probability of `w + Σ_{n ∈ s} aₙ Xₙ` is at most `(2π)⁻⁴` times the explicit
four-phase constant `fourPhaseConst`, uniformly in the conditioning `w`. -/
theorem block_smallball_caustic
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (a : ℕ → ℝ) (w : ℂ)
    {t σ0 sstar : ℝ} {J : ℕ}
    (p1 p2 p3 p4 : ℕ) (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (hp3 : p3 ∈ s) (hp4 : p4 ∈ s)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hA : (a p4:ℂ) ≠ 0) (hB : (a p3:ℂ) ≠ 0) (hC : (a p2:ℂ) ≠ 0) (hD : (a p1:ℂ) ≠ 0)
    (hρB : ‖(a p3:ℂ)‖ < ‖(a p4:ℂ)‖) (hr0 : 0 < t)
    (hr2 : 2 * t ≤ ‖(a p4:ℂ)‖ - ‖(a p3:ℂ)‖) (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖(a p4:ℂ)‖ + ‖(a p3:ℂ)‖) ^ 2 - (‖(a p4:ℂ)‖ - ‖(a p3:ℂ)‖) ^ 2) / 3)
    (hJ : ((‖(a p4:ℂ)‖ + ‖(a p3:ℂ)‖) ^ 2 - (‖(a p4:ℂ)‖ - ‖(a p3:ℂ)‖) ^ 2) / 3
        < 2 ^ J * σ0)
    (hHσ0 : 2 * (t * (2 * ‖(a p4:ℂ)‖ + t)
        / ((‖(a p4:ℂ)‖ - ‖(a p3:ℂ)‖) * ‖(a p3:ℂ)‖))
        ≤ σ0 * causticKappa ‖(a p4:ℂ)‖ ‖(a p3:ℂ)‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖(a p1:ℂ)‖) :
    steinhausMeasure {ω : Omega | ‖w + ∑ n ∈ s, (a n:ℂ) * X n ω‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
          * Sublevel.fourPhaseConst (a p4:ℂ) (a p3:ℂ) (a p2:ℂ) (a p1:ℂ) t σ0 sstar J :=
  block_smallball_condition s hs a w t p1 p2 p3 p4 hp1 hp2 hp3 hp4
    h12 h13 h14 h23 h24 h34
    (Sublevel.fourPhaseConst (a p4:ℂ) (a p3:ℂ) (a p2:ℂ) (a p1:ℂ) t σ0 sstar J)
    (fun V => Sublevel.four_phase_nested_uniform (w := V) hA hB hC hD hρB hr0 hr2
      hσ0 hσ0G hJ hHσ0 hss hss2)

end SteinhausModel
end RHTower
