import GaloisForLFunctions.HTGeometry.GaussianRadialActionKernel

/-!
# Radial Gaussian observation of a finite spectral packet

A finite packet of spectral characters observed through a Gaussian radial clock
is multiplied, character by character, by the universal radial Fourier kernel at
the dimensionless action `time · detuning`.  As the observation time grows, every
nonzero action is dephased and exactly the zero-action sector survives.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- A finite spectral packet sampled at radius `r` and time `time`. -/
def radialSpectralPacket (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (time r : ℝ) : ℂ :=
  ∑ i ∈ support, coefficient i *
    Complex.exp (-((time * detuning i * r : ℝ) : ℂ) * Complex.I)

/-- A radial character is integrable against any probability measure. -/
theorem integrable_radialCharacter {m : ℕ} (c : ℂ) (a : ℝ) :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin m) =>
        c * Complex.exp (-((a * ‖x‖ : ℝ) : ℂ) * Complex.I))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  refine Integrable.mono' (integrable_const ‖c‖) ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    fun_prop
  · filter_upwards with x
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Exact radial observer--spectral action law.**  Gaussian radial averaging of
a finite spectral packet evaluates the universal radial kernel at every
dimensionless action. -/
theorem integral_radialSpectralPacket {m : ℕ} (hm : 0 < m)
    (support : Finset ι) (coefficient : ι → ℂ) (detuning : ι → ℝ) (time : ℝ) :
    (∫ x, radialSpectralPacket support coefficient detuning time ‖x‖
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      = ∑ i ∈ support, coefficient i * radialActionKernel m (time * detuning i) := by
  have hterm : ∀ i : ι,
      (fun x : EuclideanSpace ℝ (Fin m) =>
        coefficient i * Complex.exp (-((time * detuning i * ‖x‖ : ℝ) : ℂ) * Complex.I))
        = fun x : EuclideanSpace ℝ (Fin m) =>
          coefficient i *
            Complex.exp (-(((time * detuning i) * ‖x‖ : ℝ) : ℂ) * Complex.I) := by
    intro i
    funext x
    ring_nf
  simp only [radialSpectralPacket]
  rw [integral_finsetSum support (fun i _ => by
    rw [hterm i]
    exact integrable_radialCharacter (coefficient i) (time * detuning i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hterm i, integral_const_mul, radialActionKernel_eq_integral_stdGaussian hm]

/-- Every nonzero detuning leaves every compact set under unbounded
observation. -/
theorem tendsto_mul_atTop_cocompact {d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun t : ℝ => t * d) atTop (cocompact ℝ) := by
  rw [cocompact_eq_atBot_atTop]
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · exact le_sup_of_le_left (Filter.Tendsto.atTop_mul_const_of_neg hneg tendsto_id)
  · exact le_sup_of_le_right (Filter.Tendsto.atTop_mul_const hpos tendsto_id)

/-- Every nonzero action is dephased by an unbounded Gaussian radial clock. -/
theorem tendsto_radialActionKernel_atTop {m : ℕ} {d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun t : ℝ => radialActionKernel m (t * d)) atTop (𝓝 0) :=
  (tendsto_radialActionKernel_cocompact m).comp (tendsto_mul_atTop_cocompact hd)

/-- **Zero-action completion law.**  At unbounded Gaussian radial observation
time, exactly the zero-action sector of the packet survives. -/
theorem tendsto_integral_radialSpectralPacket_atTop {m : ℕ} (hm : 0 < m)
    (support : Finset ι) (coefficient : ι → ℂ) (detuning : ι → ℝ)
    [DecidablePred fun i => detuning i = 0] :
    Tendsto
      (fun time : ℝ =>
        ∫ x, radialSpectralPacket support coefficient detuning time ‖x‖
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
      atTop (𝓝 (∑ i ∈ support.filter fun i => detuning i = 0, coefficient i)) := by
  classical
  have hrewrite : ∀ time : ℝ,
      (∫ x, radialSpectralPacket support coefficient detuning time ‖x‖
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))))
        = ∑ i ∈ support, coefficient i * radialActionKernel m (time * detuning i) :=
    fun time => integral_radialSpectralPacket hm support coefficient detuning time
  refine Tendsto.congr (fun time => (hrewrite time).symm) ?_
  have hlimit : ∀ i ∈ support,
      Tendsto (fun time : ℝ => coefficient i * radialActionKernel m (time * detuning i))
        atTop (𝓝 (if detuning i = 0 then coefficient i else 0)) := by
    intro i _
    by_cases hi : detuning i = 0
    · rw [if_pos hi]
      have : ∀ time : ℝ, coefficient i * radialActionKernel m (time * detuning i)
          = coefficient i := by
        intro time
        rw [hi, mul_zero, radialActionKernel_zero hm, mul_one]
      exact Tendsto.congr (fun time => (this time).symm) tendsto_const_nhds
    · rw [if_neg hi]
      simpa using (tendsto_radialActionKernel_atTop (m := m) hi).const_mul (coefficient i)
  have hsum := tendsto_finsetSum support hlimit
  rw [Finset.sum_filter]
  exact hsum

end

end GaloisForLFunctions.HTGeometry
