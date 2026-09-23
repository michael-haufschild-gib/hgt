import GaloisForLFunctions.RHTower.BurnolCoPoissonIntertwiningLine
import GaloisForLFunctions.RHTower.SoninEvenCarrier

/-!
# The co-Poisson intertwining as an identity of `L^(2 : ℕ)` vectors

A vector of `L^(2 : ℕ)` is determined by its pairings against Schwartz functions, and the `L^(2 : ℕ)` Fourier
transform sends the class of a Schwartz function to the class of its Fourier transform.  So a
pairing identity of the shape

`integral phi * conj u = integral (F phi) * conj v`

for every Schwartz `phi` says exactly that `v` is the `L^(2 : ℕ)` Fourier transform of `u`.  Applied to the
co-Poisson pairing identity this turns Burnol's intertwining into the statement that the cosine
transform of a co-Poisson vector is the co-Poisson vector of the reciprocal seed.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform InnerProductSpace

noncomputable section

namespace RHTower

/-- The inner product of an `L^(2 : ℕ)` vector against the class of a Schwartz function. -/
theorem inner_toLp_eq_integral (u : SoninL2) (f : SchwartzMap ℝ ℂ) :
    ⟪u, f.toLp 2 volume⟫_ℂ =
      ∫ t : ℝ, (f : ℝ → ℂ) t * (starRingEnd ℂ) ((u : ℝ → ℂ) t) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp f 2 volume] with t ht
  rw [RCLike.inner_apply, ht]

/-- **A vector is determined by its Schwartz pairings, through the Fourier transform.** -/
theorem fourierUnitary_eq_of_schwartz_pairing {u v : SoninL2}
    (h : ∀ φ : SchwartzMap ℝ ℂ,
      (∫ t : ℝ, (φ : ℝ → ℂ) t * (starRingEnd ℂ) ((u : ℝ → ℂ) t)) =
        ∫ t : ℝ, (𝓕 (φ : ℝ → ℂ)) t * (starRingEnd ℂ) ((v : ℝ → ℂ) t)) :
    fourierUnitary u = v := by
  have hdense : DenseRange fun φ : SchwartzMap ℝ ℂ => fourierUnitary (φ.toLp 2 volume) := by
    have h1 : DenseRange fun φ : SchwartzMap ℝ ℂ => (φ.toLp 2 volume : SoninL2) := by
      have hd : DenseRange ⇑(SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
        SchwartzMap.denseRange_toLpCLM (by simp)
      convert hd using 1
      funext φ
      exact SchwartzMap.toLpCLM_apply.symm
    exact (fourierUnitary.surjective.denseRange).comp h1 fourierUnitary.continuous
  set d : SoninL2 := fourierUnitary u - v with hd
  have hzero : ∀ z : SoninL2, ⟪d, z⟫_ℂ = 0 := by
    intro z
    refine DenseRange.induction_on (p := fun z => ⟪d, z⟫_ℂ = 0) hdense z ?_ ?_
    · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
    · intro φ
      have hfour : fourierUnitary (φ.toLp 2 volume) = (𝓕 φ).toLp 2 volume :=
        SchwartzMap.toLp_fourier_eq φ
      have hcoe : ∀ t : ℝ, ((𝓕 φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t = (𝓕 (φ : ℝ → ℂ)) t := by
        intro t
        rw [SchwartzMap.fourier_coe]
      have hEq : (∫ t : ℝ, ((𝓕 φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) t *
            (starRingEnd ℂ) ((v : ℝ → ℂ) t)) =
          ∫ t : ℝ, (𝓕 (φ : ℝ → ℂ)) t * (starRingEnd ℂ) ((v : ℝ → ℂ) t) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        dsimp only
        rw [hcoe t]
      rw [hd, inner_sub_left, fourierUnitary.inner_map_map, hfour,
        inner_toLp_eq_integral, inner_toLp_eq_integral, hEq, h φ, sub_self]
  have : d = 0 := inner_self_eq_zero.mp (hzero d)
  rwa [hd, sub_eq_zero] at this

/-- **Burnol's co-Poisson intertwining as an identity of `L^(2 : ℕ)` vectors.**  The `L^(2 : ℕ)` Fourier
transform of the co-Poisson vector of a window seed is the co-Poisson vector of the reciprocal
seed. -/
theorem fourierUnitary_coPoissonVector {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    (hG : Integrable (coPoissonReciprocalSeed g))
    (hGsupp : Function.support (coPoissonReciprocalSeed g) ⊆ Icc b b⁻¹)
    (hPm : Measurable (burnolCoPoissonRightSum g)) {K : ℝ}
    (hPb : ∀ t : ℝ, ‖burnolCoPoissonRightSum g t‖ ≤ K)
    (hPGm : Measurable (burnolCoPoissonRightSum (coPoissonReciprocalSeed g))) {K' : ℝ}
    (hPGb : ∀ t : ℝ, ‖burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t‖ ≤ K')
    (hPreal : ∀ t : ℝ,
      (starRingEnd ℂ) (burnolCoPoissonRightSum g t) = burnolCoPoissonRightSum g t)
    (hPGreal : ∀ t : ℝ, (starRingEnd ℂ) (burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t) =
      burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t)
    (hPmem : MemLp (burnolCoPoissonRightSum g) 2 volume)
    (hPGmem : MemLp (burnolCoPoissonRightSum (coPoissonReciprocalSeed g)) 2 volume) :
    fourierUnitary (hPmem.toLp _) = hPGmem.toLp _ := by
  refine fourierUnitary_eq_of_schwartz_pairing fun φ => ?_
  have hleft : (∫ t : ℝ, (φ : ℝ → ℂ) t *
      (starRingEnd ℂ) (((hPmem.toLp _ : SoninL2) : ℝ → ℂ) t)) =
      ∫ t : ℝ, burnolCoPoissonRightSum g t * (φ : ℝ → ℂ) t := by
    refine integral_congr_ae ?_
    filter_upwards [hPmem.coeFn_toLp] with t ht
    rw [ht, hPreal t, mul_comm]
  have hright : (∫ t : ℝ, (𝓕 (φ : ℝ → ℂ)) t *
      (starRingEnd ℂ) (((hPGmem.toLp _ : SoninL2) : ℝ → ℂ) t)) =
      ∫ t : ℝ, burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t * (𝓕 (φ : ℝ → ℂ)) t := by
    refine integral_congr_ae ?_
    filter_upwards [hPGmem.coeFn_toLp] with t ht
    rw [ht, hPGreal t, mul_comm]
  rw [hleft, hright]
  exact integral_line_burnolCoPoisson_mul_eq_fourier hb hg hsupp hG hGsupp hPm hPb hPGm hPGb φ

end RHTower

