/-
Carrier-free anchor instruments on the critical line, and the general-coefficient
anchor supply.

Any value of the form `w + χ·conj w` on the line — the shape shared by every
χ-symmetrized real-coefficient carrier — has modulus `|2·Re(ω̄·w)|`, where `ω` is the
unimodular Hardy square-root of χ; squaring splits the energy as
`‖w + χ·conj w‖² = 4‖w‖² − 4·Im(ω̄w)²`.  A generic mean-value floor turns a strict
second-moment inequality into a pointwise floor inside every prescribed window.
Instantiated for the general finite Dirichlet carrier: its critical-line values are the
mean-value theory's Dirichlet polynomial in the coefficients `b_n·n^{−1/2}`, so a
diagonal-vs-off-diagonal energy face produces, in every window, a height where the
χ-symmetrized carrier clears a prescribed floor, and the archimedean floor upgrades it
to a pointwise anchor for `|Re|` of the completed carrier — the anchor face of the mass
machinery, for arbitrary designed coefficients.
-/
import GaloisForLFunctions.RHTower.MollifiedCarrier
import GaloisForLFunctions.RHTower.SecondMoment

open Complex Metric MeasureTheory

namespace RHTower

/-! ### §1 Carrier-free phase instruments -/

/-- **Phase collapse on the line.**  For any `w`, the χ-symmetrized combination
`w + χ·conj w` is a unimodular phase times the real amplitude `2·Re(ω̄w)`. -/
private theorem norm_add_chi_mul_conj_eq (τ : ℝ) (w : ℂ) :
    ‖w + zetaChi (linePt τ) * (starRingEnd ℂ) w‖ =
      |2 * (((starRingEnd ℂ) (hardyPhase τ)) * w).re| := by
  set ω := hardyPhase τ with hω
  have hcw : (starRingEnd ℂ) ω * ω = 1 := conj_hardyPhase_mul_self τ
  have hw2 : ω * ω = zetaChi (linePt τ) := hardyPhase_sq τ
  have key : (starRingEnd ℂ) ω * (w + zetaChi (linePt τ) * (starRingEnd ℂ) w)
      = ((starRingEnd ℂ) ω * w) + (starRingEnd ℂ) ((starRingEnd ℂ) ω * w) := by
    rw [← hw2, map_mul, Complex.conj_conj]
    linear_combination ((starRingEnd ℂ) w * ω) * hcw
  have h1 : ‖w + zetaChi (linePt τ) * (starRingEnd ℂ) w‖ =
      ‖(starRingEnd ℂ) ω * (w + zetaChi (linePt τ) * (starRingEnd ℂ) w)‖ := by
    rw [norm_mul, Complex.norm_conj, hω, norm_hardyPhase, one_mul]
  rw [h1, key, Complex.add_conj, Complex.norm_real, Real.norm_eq_abs]

/-- **Energy split on the line.**  The squared modulus of the χ-symmetrized combination
is four times the raw energy minus four times the orthogonal (imaginary) component. -/
private theorem norm_add_chi_mul_conj_sq_split (τ : ℝ) (w : ℂ) :
    ‖w + zetaChi (linePt τ) * (starRingEnd ℂ) w‖ ^ 2 =
      4 * ‖w‖ ^ 2 - 4 * (((starRingEnd ℂ) (hardyPhase τ)) * w).im ^ 2 := by
  rw [norm_add_chi_mul_conj_eq, sq_abs]
  set z := (starRingEnd ℂ) (hardyPhase τ) * w with hz
  have hnz : ‖z‖ = ‖w‖ := by
    rw [hz, norm_mul, Complex.norm_conj, norm_hardyPhase, one_mul]
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [← hnz, hsq]
  ring

/-! ### §2 The generic mean-value floor -/

/-- **Generic window floor.**  Any detector whose window second moment strictly exceeds
`m²·U` clears the floor `m` somewhere in the window. -/
private theorem exists_norm_floor_in_window_of_secondMoment {G : ℝ → ℂ} {T U m : ℝ}
    (hU : 0 < U) (hGc : Continuous fun τ => ‖G τ‖ ^ 2)
    (hmoment : m ^ 2 * U < ∫ τ in T..(T + U), ‖G τ‖ ^ 2) :
    ∃ τ ∈ Set.Icc T (T + U), m < ‖G τ‖ := by
  by_contra hcon
  push Not at hcon
  have hup : (∫ τ in T..(T + U), ‖G τ‖ ^ 2) ≤ m ^ 2 * U := by
    have hmono := intervalIntegral.integral_mono_on
      (g := fun _ => m ^ 2) (μ := volume) (by linarith : T ≤ T + U)
      (hGc.intervalIntegrable T (T + U)) intervalIntegrable_const
      (fun τ hτ => by nlinarith [norm_nonneg (G τ), hcon τ hτ])
    calc (∫ τ in T..(T + U), ‖G τ‖ ^ 2) ≤ ∫ _ in T..(T + U), m ^ 2 := hmono
      _ = m ^ 2 * U := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  linarith

/-! ### §3 Continuity of the general carrier along the line -/

private theorem continuous_mollPoly_line (b : ℕ → ℝ) (N : ℕ) :
    Continuous fun τ : ℝ => mollPoly b N (linePt τ) := by
  have heq : (fun τ : ℝ => mollPoly b N (linePt τ)) =
      fun τ : ℝ => ∑ n ∈ Finset.Icc 1 N, ((b n : ℝ) : ℂ) *
        ((((n : ℝ) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (Real.log n : ℂ)) * τ)) := by
    funext τ
    unfold mollPoly
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [natCast_cpow_neg_linePt n (Finset.mem_Icc.mp hn).1 τ]
  rw [heq]
  apply continuous_finsetSum
  intro n _
  fun_prop

private theorem continuous_zetaChi_line : Continuous fun τ : ℝ => zetaChi (linePt τ) := by
  rw [continuous_iff_continuousAt]
  intro τ
  have h1 : ContinuousAt zetaChi (linePt τ) := by
    apply (zetaChi_analyticAt ?_).continuousAt
    have hre : (1 - linePt τ).re = 1 / 2 := by
      unfold linePt
      simp
      norm_num
    exact Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num)
  have hlin : ContinuousAt linePt τ := by
    unfold linePt
    fun_prop
  show ContinuousAt (zetaChi ∘ linePt) τ
  exact ContinuousAt.comp h1 hlin

/-- The conjugated-reflection form of the general carrier on the line. -/
private theorem mollG_line_conjForm (b : ℕ → ℝ) (N : ℕ) (τ : ℝ) :
    mollG b N (linePt τ) = mollPoly b N (linePt τ) +
      zetaChi (linePt τ) * (starRingEnd ℂ) (mollPoly b N (linePt τ)) := by
  unfold mollG chiSymmetrize
  rw [← conj_linePt, mollPoly_conj]

private theorem continuous_mollG_line (b : ℕ → ℝ) (N : ℕ) :
    Continuous fun τ : ℝ => mollG b N (linePt τ) := by
  have heq : (fun τ : ℝ => mollG b N (linePt τ)) = fun τ : ℝ =>
      mollPoly b N (linePt τ) +
        zetaChi (linePt τ) * (starRingEnd ℂ) (mollPoly b N (linePt τ)) :=
    funext fun τ => mollG_line_conjForm b N τ
  rw [heq]
  exact (continuous_mollPoly_line b N).add
    (continuous_zetaChi_line.mul
      (Complex.continuous_conj.comp (continuous_mollPoly_line b N)))

/-! ### §4 The general-coefficient anchor supply -/

/-- On the critical line the general carrier is the mean-value theory's Dirichlet
polynomial in the coefficients `b_n·n^{−1/2}`. -/
private theorem mollPoly_line_eq_dpoly (b : ℕ → ℝ) (N : ℕ) (u : ℝ) :
    mollPoly b N (linePt u) =
      dpoly (fun n => b n * ((n : ℝ) ^ (-(1/2 : ℝ)))) (Finset.Icc 1 N) u := by
  unfold mollPoly dpoly cterm
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [natCast_cpow_neg_linePt n (Finset.mem_Icc.mp hn).1 u]
  have hexp : Complex.exp (-(Complex.I * (Real.log n : ℂ)) * (u : ℂ)) =
      Complex.exp (-(u : ℂ) * Complex.I * (Real.log n : ℂ)) := by
    congr 1
    ring
  rw [hexp]
  push_cast
  ring

/-- **Every-window anchor for the general carrier.**  If the orthogonal-corrected energy
budget clears the diagonal-vs-off-diagonal mean-value threshold of the coefficients
`b_n·n^{−1/2}`, then every window of length `U` contains a height where the
χ-symmetrized general carrier clears the floor `m`. -/
private theorem exists_mollG_line_anchor_in_window_of_orthogonal_energy
    (b : ℕ → ℝ) (N : ℕ) {T U m : ℝ} (hU : 0 < U)
    (henergy : m ^ 2 * U +
        (∫ τ in T..(T + U),
          4 * ((((starRingEnd ℂ) (hardyPhase τ)) * mollPoly b N (linePt τ)).im) ^ 2) <
      4 * (U * (∑ n ∈ Finset.Icc 1 N, (b n * ((n : ℝ) ^ (-(1/2 : ℝ)))) ^ 2)
        - ∑ p ∈ Finset.Icc 1 N, ∑ q ∈ (Finset.Icc 1 N).erase p,
            2 * |(b p * ((p : ℝ) ^ (-(1/2 : ℝ)))) * (b q * ((q : ℝ) ^ (-(1/2 : ℝ))))|
              / |Real.log q - Real.log p|)) :
    ∃ τ ∈ Set.Icc T (T + U), m ≤ ‖mollG b N (linePt τ)‖ := by
  have hconth : Continuous fun τ : ℝ => ‖mollPoly b N (linePt τ)‖ ^ 2 :=
    (continuous_mollPoly_line b N).norm.pow 2
  have hcontG : Continuous fun τ : ℝ => ‖mollG b N (linePt τ)‖ ^ 2 :=
    (continuous_mollG_line b N).norm.pow 2
  have hsplit : ∀ τ : ℝ,
      4 * ((((starRingEnd ℂ) (hardyPhase τ)) * mollPoly b N (linePt τ)).im) ^ 2 =
        4 * ‖mollPoly b N (linePt τ)‖ ^ 2 - ‖mollG b N (linePt τ)‖ ^ 2 := by
    intro τ
    have h := norm_add_chi_mul_conj_sq_split τ (mollPoly b N (linePt τ))
    rw [mollG_line_conjForm]
    linarith
  have hIm_int : (∫ τ in T..(T + U),
      4 * ((((starRingEnd ℂ) (hardyPhase τ)) * mollPoly b N (linePt τ)).im) ^ 2) =
      4 * (∫ τ in T..(T + U), ‖mollPoly b N (linePt τ)‖ ^ 2) -
        (∫ τ in T..(T + U), ‖mollG b N (linePt τ)‖ ^ 2) := by
    rw [intervalIntegral.integral_congr (g := fun τ =>
      4 * ‖mollPoly b N (linePt τ)‖ ^ 2 - ‖mollG b N (linePt τ)‖ ^ 2)
      (fun τ _ => hsplit τ)]
    rw [intervalIntegral.integral_sub
      ((hconth.const_mul 4).intervalIntegrable T (T + U))
      (hcontG.intervalIntegrable T (T + U)),
      intervalIntegral.integral_const_mul]
  have hbridge : (∫ τ in T..(T + U), ‖mollPoly b N (linePt τ)‖ ^ 2) =
      ∫ τ in T..(T + U),
        ‖dpoly (fun n => b n * ((n : ℝ) ^ (-(1/2 : ℝ)))) (Finset.Icc 1 N) τ‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun τ _ => ?_
    rw [mollPoly_line_eq_dpoly]
  have hMV : U * (∑ n ∈ Finset.Icc 1 N, (b n * ((n : ℝ) ^ (-(1/2 : ℝ)))) ^ 2)
        - ∑ p ∈ Finset.Icc 1 N, ∑ q ∈ (Finset.Icc 1 N).erase p,
            2 * |(b p * ((p : ℝ) ^ (-(1/2 : ℝ)))) * (b q * ((q : ℝ) ^ (-(1/2 : ℝ))))|
              / |Real.log q - Real.log p|
      ≤ ∫ τ in T..(T + U),
        ‖dpoly (fun n => b n * ((n : ℝ) ^ (-(1/2 : ℝ)))) (Finset.Icc 1 N) τ‖ ^ 2 :=
    secondMoment_lower_bound _ _ T U (fun n hn => (Finset.mem_Icc.mp hn).1)
  have hmoment : m ^ 2 * U < ∫ τ in T..(T + U), ‖mollG b N (linePt τ)‖ ^ 2 := by
    rw [hIm_int, hbridge] at henergy
    linarith
  obtain ⟨τ, hτ, hlt⟩ :=
    exists_norm_floor_in_window_of_secondMoment hU hcontG hmoment
  exact ⟨τ, hτ, hlt.le⟩

/-- **Every-window anchor for the completed general carrier.**  The energy face plus an
archimedean floor produce, in every window, a height with the pointwise anchor
`a₀·m ≤ |Re|` — the input of the point-to-mass converter, for arbitrary designed
coefficients. -/
theorem exists_re_completedMollG_anchor_in_window_of_orthogonal_energy
    (b : ℕ → ℝ) (N : ℕ) {T U m a₀ : ℝ} (hU : 0 < U) (hm0 : 0 ≤ m)
    (ha₀ : ∀ τ ∈ Set.Icc T (T + U), a₀ ≤ ‖archFactor (linePt τ)‖)
    (henergy : m ^ 2 * U +
        (∫ τ in T..(T + U),
          4 * ((((starRingEnd ℂ) (hardyPhase τ)) * mollPoly b N (linePt τ)).im) ^ 2) <
      4 * (U * (∑ n ∈ Finset.Icc 1 N, (b n * ((n : ℝ) ^ (-(1/2 : ℝ)))) ^ 2)
        - ∑ p ∈ Finset.Icc 1 N, ∑ q ∈ (Finset.Icc 1 N).erase p,
            2 * |(b p * ((p : ℝ) ^ (-(1/2 : ℝ)))) * (b q * ((q : ℝ) ^ (-(1/2 : ℝ))))|
              / |Real.log q - Real.log p|)) :
    ∃ τ ∈ Set.Icc T (T + U), a₀ * m ≤ |(completedMollG b N (linePt τ)).re| := by
  obtain ⟨τ, hτ, hm⟩ :=
    exists_mollG_line_anchor_in_window_of_orthogonal_energy b N hU henergy
  exact ⟨τ, hτ, anchor_re_completedMollG_line_of_floors b N hm0 (ha₀ τ hτ) hm⟩

end RHTower
