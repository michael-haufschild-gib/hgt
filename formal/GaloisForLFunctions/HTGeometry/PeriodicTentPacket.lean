import GaloisForLFunctions.HTGeometry.TorusFejerDisplacement
import GaloisForLFunctions.HTGeometry.WindowMeanSeparatedModes

/-!
# The periodic tent

The tent of width `ρ` becomes a genuine function on the circle once its argument is measured by the
distance to the lattice of whole turns rather than by the absolute value.  That distance is an
infimum of translates of the absolute value, so it is automatically `1`-Lipschitz, and it is
invariant under a whole turn because the lattice is.  On the fundamental window `|x| ≤ π` it agrees
with `|x|`, so for a width `ρ ≤ π` the periodic tent has the same mass, the same positivity set and
the same Lipschitz constant as the tent built from `|x|`.

Consequently every displacement estimate proved for a Lipschitz function applies verbatim to the
periodic tent, and the resulting Fejér mean is a function on the circle.
-/

open Real intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section TurnDistance

/-- The lattice of whole turns. -/
def turnLattice : Set ℝ := Set.range fun n : ℤ => 2 * π * (n : ℝ)

theorem zero_mem_turnLattice : (0 : ℝ) ∈ turnLattice := ⟨0, by simp⟩

theorem turnLattice_nonempty : turnLattice.Nonempty := ⟨0, zero_mem_turnLattice⟩

theorem add_turn_mem_turnLattice {y : ℝ} (hy : y ∈ turnLattice) : y + 2 * π ∈ turnLattice := by
  obtain ⟨n, hn⟩ := hy
  exact ⟨n + 1, by push_cast [← hn]; ring⟩

theorem sub_turn_mem_turnLattice {y : ℝ} (hy : y ∈ turnLattice) : y - 2 * π ∈ turnLattice := by
  obtain ⟨n, hn⟩ := hy
  exact ⟨n - 1, by push_cast [← hn]; ring⟩

/-- The distance from a real number to the nearest whole turn. -/
def turnDist (x : ℝ) : ℝ := Metric.infDist x turnLattice

theorem turnDist_nonneg (x : ℝ) : 0 ≤ turnDist x := Metric.infDist_nonneg

theorem turnDist_le_abs (x : ℝ) : turnDist x ≤ |x| := by
  have h := Metric.infDist_le_dist_of_mem (x := x) zero_mem_turnLattice
  rw [turnDist]
  simpa [Real.dist_eq] using h

/-- The turn distance is `1`-Lipschitz, being an infimum of translates of the absolute value. -/
theorem abs_turnDist_sub_le (u v : ℝ) : |turnDist u - turnDist v| ≤ |u - v| := by
  have h := (Metric.lipschitz_infDist_pt turnLattice).dist_le_mul u v
  rw [Real.dist_eq, Real.dist_eq] at h
  rw [turnDist, turnDist]
  simpa using h

theorem continuous_turnDist : Continuous turnDist :=
  (Metric.lipschitz_infDist_pt turnLattice).continuous

/-- A whole turn leaves the turn distance unchanged. -/
theorem periodic_turnDist : Function.Periodic turnDist (2 * π) := by
  intro x
  refine le_antisymm ?_ ?_
  · refine (Metric.le_infDist turnLattice_nonempty).mpr fun y hy => ?_
    have hmem : y + 2 * π ∈ turnLattice := add_turn_mem_turnLattice hy
    have h := Metric.infDist_le_dist_of_mem (x := x + 2 * π) hmem
    rwa [Real.dist_eq, show x + 2 * π - (y + 2 * π) = x - y by ring, ← Real.dist_eq] at h
  · refine (Metric.le_infDist turnLattice_nonempty).mpr fun y hy => ?_
    have hmem : y - 2 * π ∈ turnLattice := sub_turn_mem_turnLattice hy
    have h := Metric.infDist_le_dist_of_mem (x := x) hmem
    rwa [Real.dist_eq, show x - (y - 2 * π) = x + 2 * π - y by ring, ← Real.dist_eq] at h

/-- On the fundamental window the turn distance is the absolute value. -/
theorem turnDist_eq_abs {x : ℝ} (hx : |x| ≤ π) : turnDist x = |x| := by
  refine le_antisymm (turnDist_le_abs x) ?_
  refine (Metric.le_infDist turnLattice_nonempty).mpr ?_
  rintro y ⟨n, rfl⟩
  rw [Real.dist_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hpi : (0 : ℝ) < π := Real.pi_pos
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
        _ = |(n : ℝ)| := by push_cast [Int.cast_abs]; rfl
    have hbig : 2 * π ≤ |2 * π * (n : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
      nlinarith
    have htri : |2 * π * (n : ℝ)| - |x| ≤ |x - 2 * π * (n : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (2 * π * (n : ℝ)) x
      rwa [abs_sub_comm (2 * π * (n : ℝ)) x] at this
    linarith

end TurnDistance

section PeriodicTent

/-- The tent of width `ρ` on the circle: the tent profile of the turn distance. -/
def perTent (ρ x : ℝ) : ℝ := max (1 - turnDist x / ρ) 0

theorem perTent_nonneg (ρ x : ℝ) : 0 ≤ perTent ρ x := le_max_right _ _

theorem perTent_le_one {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) : perTent ρ x ≤ 1 := by
  refine max_le ?_ zero_le_one
  have : (0 : ℝ) ≤ turnDist x / ρ := by
    have := turnDist_nonneg x
    positivity
  linarith

theorem periodic_perTent (ρ : ℝ) : Function.Periodic (perTent ρ) (2 * π) := by
  intro x
  rw [perTent, perTent, periodic_turnDist x]

theorem continuous_perTent (ρ : ℝ) : Continuous (perTent ρ) := by
  unfold perTent
  exact (continuous_const.sub (continuous_turnDist.div_const ρ)).max continuous_const

/-- The positivity set of the periodic tent is the open turn-ball of radius `ρ`. -/
theorem perTent_pos_iff {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) : 0 < perTent ρ x ↔ turnDist x < ρ := by
  rw [perTent, lt_max_iff]
  constructor
  · rintro (h | h)
    · rw [lt_sub_iff_add_lt, zero_add, div_lt_one hρ] at h
      exact h
    · exact absurd h (lt_irrefl 0)
  · intro h
    left
    rw [lt_sub_iff_add_lt, zero_add, div_lt_one hρ]
    exact h

/-- **The periodic tent is `1/ρ`-Lipschitz.** -/
theorem abs_perTent_sub_le {ρ : ℝ} (hρ : 0 < ρ) (u v : ℝ) :
    |perTent ρ u - perTent ρ v| ≤ (1 / ρ) * |u - v| := by
  have hmax : |perTent ρ u - perTent ρ v|
      ≤ |(1 - turnDist u / ρ) - (1 - turnDist v / ρ)| := by
    unfold perTent
    exact abs_max_sub_max_le_abs _ _ _
  have heq : (1 - turnDist u / ρ) - (1 - turnDist v / ρ) = (turnDist v - turnDist u) / ρ := by
    ring
  have habs : |turnDist v - turnDist u| ≤ |u - v| := by
    have := abs_turnDist_sub_le v u
    rwa [show v - u = -(u - v) by ring, abs_neg] at this
  calc |perTent ρ u - perTent ρ v| ≤ |(1 - turnDist u / ρ) - (1 - turnDist v / ρ)| := hmax
    _ = |turnDist v - turnDist u| / ρ := by rw [heq, abs_div, abs_of_pos hρ]
    _ ≤ |u - v| / ρ := by gcongr
    _ = (1 / ρ) * |u - v| := by ring

/-- On the fundamental window the periodic tent is the tent of the absolute value. -/
theorem perTent_eq_torusTent {ρ x : ℝ} (hx : |x| ≤ π) : perTent ρ x = torusTent ρ x := by
  rw [perTent, torusTent, turnDist_eq_abs hx]

/-- **The mass of the periodic tent.**  For a width at most `π` it is the same as the tent's. -/
theorem integral_perTent {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π) :
    (∫ x in (-π)..π, perTent ρ x) = ρ := by
  have hcongr : (∫ x in (-π)..π, perTent ρ x) = ∫ x in (-π)..π, torusTent ρ x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx
    exact perTent_eq_torusTent (abs_le.mpr ⟨hx.1, hx.2⟩)
  rw [hcongr, integral_torusTent hρ hρπ]

/-- **`(16)` for the periodic tent.** -/
theorem abs_fejerConv_perTent_sub_le (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    |fejerConv N (perTent ρ) θ - perTent ρ θ| ≤ (1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1)) :=
  abs_fejerConv_sub_le N (by positivity) (fun u v => abs_perTent_sub_le hρ u v) θ

end PeriodicTent

section PeriodicProduct

variable {d : ℕ}

/-- The `d`-fold periodic tent centred at `c`. -/
def periodicProductTent (ρ : ℝ) (c θ : Fin d → ℝ) : ℝ := ∏ j, perTent ρ (θ j - c j)

/-- The Fejér mean of the `d`-fold periodic tent: by Fubini the convolution against the product
kernel factorizes into the one-dimensional Fejér means. -/
def periodicProductFejerTent (N : ℕ) (ρ : ℝ) (c θ : Fin d → ℝ) : ℝ :=
  ∏ j, fejerConv N (perTent ρ) (θ j - c j)

/-- **`(16)` in `d` dimensions, on the circle.** -/
theorem abs_periodicProductFejerTent_sub_le (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (c θ : Fin d → ℝ) :
    |periodicProductFejerTent N ρ c θ - periodicProductTent ρ c θ|
      ≤ (d : ℝ) * ((1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1))) := by
  classical
  have hcontT : Continuous (perTent ρ) := continuous_perTent ρ
  have hb : ∀ j : Fin d, |perTent ρ (θ j - c j)| ≤ 1 := by
    intro j
    rw [abs_of_nonneg (perTent_nonneg _ _)]
    exact perTent_le_one hρ _
  have ha : ∀ j : Fin d, |fejerConv N (perTent ρ) (θ j - c j)| ≤ 1 := by
    intro j
    rw [abs_of_nonneg (fejerConv_nonneg N (fun y => perTent_nonneg ρ y) _)]
    exact fejerConv_le_one N hcontT (fun y => perTent_le_one hρ y) _
  have htele := abs_prod_sub_prod_le (Finset.univ : Finset (Fin d))
    (fun j => fejerConv N (perTent ρ) (θ j - c j)) (fun j => perTent ρ (θ j - c j))
    (fun j _ => ha j) (fun j _ => hb j)
  refine le_trans htele ?_
  calc ∑ j : Fin d, |fejerConv N (perTent ρ) (θ j - c j) - perTent ρ (θ j - c j)|
      ≤ ∑ _j : Fin d, (1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1)) :=
        Finset.sum_le_sum fun j _ => abs_fejerConv_perTent_sub_le N hρ _
    _ = (d : ℝ) * ((1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end PeriodicProduct

section PeriodicFourier

/-- The `m`-th Fourier coefficient of a `2π`-periodic function, in Haar normalization. -/
def perFourierCoeff (f : ℝ → ℝ) (m : ℝ) : ℂ :=
  ((1 / (2 * π) : ℝ) : ℂ) * ∫ y in (-π)..π, (f y : ℂ) * Complex.exp ((-(m * y) : ℝ) * Complex.I)

/-- The integrand of an integer Fourier coefficient of a periodic function is periodic. -/
theorem periodic_fourierIntegrand {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π)) (n : ℤ) :
    Function.Periodic
      (fun y : ℝ => (f y : ℂ) * Complex.exp ((-((n : ℝ) * y) : ℝ) * Complex.I)) (2 * π) := by
  intro y
  show (f (y + 2 * π) : ℂ) * Complex.exp ((-((n : ℝ) * (y + 2 * π)) : ℝ) * Complex.I)
      = (f y : ℂ) * Complex.exp ((-((n : ℝ) * y) : ℝ) * Complex.I)
  have hf : f (y + 2 * π) = f y := hper y
  have hsplit : ((-((n : ℝ) * (y + 2 * π)) : ℝ) : ℂ) * Complex.I
      = ((-((n : ℝ) * y) : ℝ) : ℂ) * Complex.I + ((-n : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hf, hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The shifted mode integral.**  Convolving a periodic function against a single character
returns the character times the corresponding Fourier coefficient. -/
theorem integral_shift_mode {f : ℝ → ℝ}
    (hper : Function.Periodic f (2 * π)) (n : ℤ) (θ : ℝ) :
    (∫ x in (-π)..π, (f (θ - x) : ℂ) * Complex.exp (((n : ℝ) * x : ℝ) * Complex.I))
      = (2 * (π : ℂ)) * perFourierCoeff f (n : ℝ)
          * Complex.exp ((((n : ℝ) * θ : ℝ)) * Complex.I) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hGper : Function.Periodic
      (fun y : ℝ => (f y : ℂ) * Complex.exp ((-((n : ℝ) * y) : ℝ) * Complex.I)) (2 * π) :=
    periodic_fourierIntegrand hper n
  have hpoint : ∀ x : ℝ, (f (θ - x) : ℂ) * Complex.exp (((n : ℝ) * x : ℝ) * Complex.I)
      = Complex.exp ((((n : ℝ) * θ : ℝ)) * Complex.I)
        * ((f (θ - x) : ℂ) * Complex.exp ((-((n : ℝ) * (θ - x)) : ℝ) * Complex.I)) := by
    intro x
    have hexp : ((((n : ℝ) * x : ℝ)) : ℂ) * Complex.I
        = ((((n : ℝ) * θ : ℝ)) : ℂ) * Complex.I
          + ((-((n : ℝ) * (θ - x)) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp, Complex.exp_add]
    ring
  have hstep1 : (∫ x in (-π)..π, (f (θ - x) : ℂ) * Complex.exp (((n : ℝ) * x : ℝ) * Complex.I))
      = Complex.exp ((((n : ℝ) * θ : ℝ)) * Complex.I)
        * ∫ x in (-π)..π, (f (θ - x) : ℂ)
            * Complex.exp ((-((n : ℝ) * (θ - x)) : ℝ) * Complex.I) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => hpoint x
  have hstep2 : (∫ x in (-π)..π, (f (θ - x) : ℂ)
        * Complex.exp ((-((n : ℝ) * (θ - x)) : ℝ) * Complex.I))
      = ∫ y in (θ - π)..(θ + π), (f y : ℂ) * Complex.exp ((-((n : ℝ) * y) : ℝ) * Complex.I) := by
    have h := intervalIntegral.integral_comp_sub_left (a := -π) (b := π)
      (fun y : ℝ => (f y : ℂ) * Complex.exp ((-((n : ℝ) * y) : ℝ) * Complex.I)) θ
    rw [h]
    congr 1
    ring
  have hstep3 : (∫ y in (θ - π)..(θ + π),
        (f y : ℂ) * Complex.exp ((-((n : ℝ) * y) : ℝ) * Complex.I))
      = ∫ y in (-π)..π, (f y : ℂ) * Complex.exp ((-((n : ℝ) * y) : ℝ) * Complex.I) := by
    have h := hGper.intervalIntegral_add_eq (θ - π) (-π)
    rw [show θ - π + 2 * π = θ + π by ring, show -π + 2 * π = π by ring] at h
    exact h
  rw [hstep1, hstep2, hstep3, perFourierCoeff]
  generalize (∫ y in (-π)..π, (f y : ℂ) * Complex.exp ((-((n : ℝ) * y) : ℝ) * Complex.I)) = X
  generalize Complex.exp ((((n : ℝ) * θ : ℝ)) * Complex.I) = E
  have hpiC : (π : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.pi_ne_zero
  push_cast
  field_simp

/-- **The Fejér mean of a periodic function is a trigonometric polynomial** whose frequencies are
the `(N+1)²` differences `p - q`, weighted by the Fourier coefficients of the function. -/
theorem fejerConv_eq_modeSum (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hper : Function.Periodic f (2 * π)) (θ : ℝ) :
    ((fejerConv N f θ : ℝ) : ℂ)
      = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          ((N : ℂ) + 1)⁻¹ * perFourierCoeff f ((p : ℝ) - (q : ℝ))
            * Complex.exp (((((p : ℝ) - (q : ℝ)) * θ) : ℝ) * Complex.I) := by
  classical
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hcontF : Continuous (torusFejer N) := continuous_torusFejer N
  have hcontfx : Continuous fun x : ℝ => f (θ - x) * torusFejer N x :=
    (hf.comp (continuous_const.sub continuous_id)).mul hcontF
  have hpush : ((∫ x in (-π)..π, f (θ - x) * torusFejer N x : ℝ) : ℂ)
      = ∫ x in (-π)..π, (f (θ - x) : ℂ) * ((torusFejer N x : ℝ) : ℂ) := by
    have h := Complex.ofRealCLM.intervalIntegral_comp_comm
      (f := fun x : ℝ => f (θ - x) * torusFejer N x) (a := -π) (b := π)
      (μ := MeasureTheory.volume) (hcontfx.intervalIntegrable _ _)
    simp only [Complex.ofRealCLM_apply] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun x _ => by rw [Complex.ofReal_mul]
  have hkernel : ∀ x : ℝ, (f (θ - x) : ℂ) * ((torusFejer N x : ℝ) : ℂ)
      = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          ((N : ℂ) + 1)⁻¹ * ((f (θ - x) : ℂ)
            * Complex.exp (((((p : ℝ) - (q : ℝ)) * x : ℝ)) * Complex.I)) := by
    intro x
    rw [torusFejer_complex, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hint : ∀ p q : ℕ, IntervalIntegrable
      (fun x : ℝ => ((N : ℂ) + 1)⁻¹ * ((f (θ - x) : ℂ)
        * Complex.exp (((((p : ℝ) - (q : ℝ)) * x : ℝ)) * Complex.I)))
      MeasureTheory.volume (-π) π := by
    intro p q
    refine Continuous.intervalIntegrable ?_ _ _
    refine continuous_const.mul (Continuous.mul ?_ ?_)
    · exact Complex.continuous_ofReal.comp (hf.comp (continuous_const.sub continuous_id))
    · fun_prop
  have hswap : (∫ x in (-π)..π, (f (θ - x) : ℂ) * ((torusFejer N x : ℝ) : ℂ))
      = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          ((N : ℂ) + 1)⁻¹ * ∫ x in (-π)..π, ((f (θ - x) : ℂ)
            * Complex.exp (((((p : ℝ) - (q : ℝ)) * x : ℝ)) * Complex.I)) := by
    rw [intervalIntegral.integral_congr (g := fun x =>
      ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          ((N : ℂ) + 1)⁻¹ * ((f (θ - x) : ℂ)
            * Complex.exp (((((p : ℝ) - (q : ℝ)) * x : ℝ)) * Complex.I)))
      (fun x _ => hkernel x)]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [intervalIntegral.integral_finsetSum (fun q _ => hint p q)]
      exact Finset.sum_congr rfl fun q _ => intervalIntegral.integral_const_mul _ _
    · intro p _
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hmode : ∀ p q : ℕ,
      (∫ x in (-π)..π, ((f (θ - x) : ℂ)
        * Complex.exp (((((p : ℝ) - (q : ℝ)) * x : ℝ)) * Complex.I)))
      = (2 * (π : ℂ)) * perFourierCoeff f ((p : ℝ) - (q : ℝ))
          * Complex.exp (((((p : ℝ) - (q : ℝ)) * θ) : ℝ) * Complex.I) := by
    intro p q
    have hcast : (((p : ℤ) - (q : ℤ) : ℤ) : ℝ) = (p : ℝ) - (q : ℝ) := by push_cast; ring
    have h := integral_shift_mode hper ((p : ℤ) - (q : ℤ)) θ
    rw [hcast] at h
    exact h
  rw [fejerConv, Complex.ofReal_mul, hpush, hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hmode p q]
  generalize perFourierCoeff f ((p : ℝ) - (q : ℝ)) = c
  generalize Complex.exp (((((p : ℝ) - (q : ℝ)) * θ) : ℝ) * Complex.I) = E
  have hpiC : (π : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.pi_ne_zero
  have hNC : ((N : ℂ) + 1) ≠ 0 := by
    have hR : ((N : ℝ) + 1) ≠ 0 := by positivity
    intro h
    exact hR (by exact_mod_cast h)
  push_cast
  field_simp

/-- **`(13)`, the coefficient bound.**  Every Fourier coefficient of a nonnegative periodic function
is bounded by its Haar mean. -/
theorem norm_perFourierCoeff_le {f : ℝ → ℝ} (hf0 : ∀ y, 0 ≤ f y) (m : ℝ) :
    ‖perFourierCoeff f m‖ ≤ (∫ y in (-π)..π, f y) / (2 * π) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hnorm : ∀ y : ℝ, ‖(f y : ℂ) * Complex.exp ((-(m * y) : ℝ) * Complex.I)‖ = f y := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 y), Complex.norm_exp]
    have hre : (((-(m * y) : ℝ) : ℂ) * Complex.I).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
  have hbound : ‖∫ y in (-π)..π, (f y : ℂ) * Complex.exp ((-(m * y) : ℝ) * Complex.I)‖
      ≤ ∫ y in (-π)..π, f y := by
    have h := intervalIntegral.norm_integral_le_abs_integral_norm
      (f := fun y : ℝ => (f y : ℂ) * Complex.exp ((-(m * y) : ℝ) * Complex.I))
      (a := -π) (b := π) (μ := MeasureTheory.volume)
    have heq : (∫ y in (-π)..π, ‖(f y : ℂ) * Complex.exp ((-(m * y) : ℝ) * Complex.I)‖)
        = ∫ y in (-π)..π, f y :=
      intervalIntegral.integral_congr fun y _ => hnorm y
    rw [heq] at h
    have hnn : 0 ≤ ∫ y in (-π)..π, f y :=
      intervalIntegral.integral_nonneg (by linarith) fun y _ => hf0 y
    rwa [abs_of_nonneg hnn] at h
  rw [perFourierCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * π))]
  calc (1 / (2 * π)) * ‖∫ y in (-π)..π, (f y : ℂ) * Complex.exp ((-(m * y) : ℝ) * Complex.I)‖
      ≤ (1 / (2 * π)) * ∫ y in (-π)..π, f y :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (∫ y in (-π)..π, f y) / (2 * π) := by ring

/-- The constant coefficient is the Haar mean. -/
theorem perFourierCoeff_zero {f : ℝ → ℝ} (hf : Continuous f) :
    perFourierCoeff f 0 = (((∫ y in (-π)..π, f y) / (2 * π) : ℝ) : ℂ) := by
  have hzero : ∀ y : ℝ, (f y : ℂ) * Complex.exp ((-(0 * y) : ℝ) * Complex.I) = ((f y : ℝ) : ℂ) := by
    intro y
    norm_num
  have hpush : (∫ y in (-π)..π, ((f y : ℝ) : ℂ)) = ((∫ y in (-π)..π, f y : ℝ) : ℂ) := by
    have h := Complex.ofRealCLM.intervalIntegral_comp_comm (f := f) (a := -π) (b := π)
      (μ := MeasureTheory.volume) (hf.intervalIntegrable _ _)
    simp only [Complex.ofRealCLM_apply] at h
    exact h
  rw [perFourierCoeff, intervalIntegral.integral_congr (fun y _ => hzero y), hpush]
  push_cast
  ring

/-- **`(13)` for the tent.**  Every Fourier coefficient of the periodic tent of width `ρ` is bounded
by its Haar mean `ρ/2π`. -/
theorem norm_perFourierCoeff_perTent_le {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π) (m : ℝ) :
    ‖perFourierCoeff (perTent ρ) m‖ ≤ ρ / (2 * π) := by
  have h := norm_perFourierCoeff_le (f := perTent ρ) (fun y => perTent_nonneg ρ y) m
  rwa [integral_perTent hρ hρπ] at h

/-- **`(11)` as a Fourier statement.**  The constant coefficient of the periodic tent is `ρ/2π`. -/
theorem perFourierCoeff_perTent_zero {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π) :
    perFourierCoeff (perTent ρ) 0 = ((ρ / (2 * π) : ℝ) : ℂ) := by
  rw [perFourierCoeff_zero (continuous_perTent ρ), integral_perTent hρ hρπ]

/-- **`(12)` for the tent.**  The Fejér mean of the periodic tent is a trigonometric polynomial
supported on the `(N+1)²` differences `p - q`, with every weight bounded by `ρ/2π` and the diagonal
weights equal to `ρ/2π`. -/
theorem fejerConv_perTent_eq_modeSum (N : ℕ) {ρ : ℝ} (θ : ℝ) :
    ((fejerConv N (perTent ρ) θ : ℝ) : ℂ)
      = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          ((N : ℂ) + 1)⁻¹ * perFourierCoeff (perTent ρ) ((p : ℝ) - (q : ℝ))
            * Complex.exp (((((p : ℝ) - (q : ℝ)) * θ) : ℝ) * Complex.I) :=
  fejerConv_eq_modeSum N (continuous_perTent ρ) (periodic_perTent ρ) θ

/-- The double sum over `p, q`, flattened to a sum over pairs. -/
theorem fejerConv_eq_pairSum (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hper : Function.Periodic f (2 * π)) (θ : ℝ) :
    ((fejerConv N f θ : ℝ) : ℂ)
      = ∑ pq ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
          ((N : ℂ) + 1)⁻¹ * perFourierCoeff f ((pq.1 : ℝ) - (pq.2 : ℝ))
            * Complex.exp (((((pq.1 : ℝ) - (pq.2 : ℝ)) * θ) : ℝ) * Complex.I) := by
  rw [Finset.sum_product]
  exact fejerConv_eq_modeSum N hf hper θ

section ProductModes

variable {d : ℕ}

/-- One mode of the `d`-dimensional packet, indexed by a tuple of pairs. -/
def packetMode (N : ℕ) (ρ : ℝ) (c θ : Fin d → ℝ) (k : Fin d → ℕ × ℕ) : ℂ :=
  ∏ j, (((N : ℂ) + 1)⁻¹ * perFourierCoeff (perTent ρ) (((k j).1 : ℝ) - ((k j).2 : ℝ))
    * Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) * (θ j - c j) : ℝ) * Complex.I))

/-- **`(12)` in `d` dimensions.**  The Fejér mean of the `d`-fold periodic tent is a finite sum of
modes indexed by tuples of pairs from `{0,…,N}`. -/
theorem periodicProductFejerTent_eq_modeSum (N : ℕ) (ρ : ℝ) (c θ : Fin d → ℝ) :
    ((periodicProductFejerTent N ρ c θ : ℝ) : ℂ)
      = ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1)),
          packetMode N ρ c θ k := by
  classical
  rw [periodicProductFejerTent, Complex.ofReal_prod]
  have hfac : ∀ j : Fin d, ((fejerConv N (perTent ρ) (θ j - c j) : ℝ) : ℂ)
      = ∑ pq ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
          ((N : ℂ) + 1)⁻¹ * perFourierCoeff (perTent ρ) ((pq.1 : ℝ) - (pq.2 : ℝ))
            * Complex.exp (((((pq.1 : ℝ) - (pq.2 : ℝ)) * (θ j - c j)) : ℝ) * Complex.I) :=
    fun j => fejerConv_eq_pairSum N (continuous_perTent ρ) (periodic_perTent ρ) _
  rw [Finset.prod_congr rfl fun j _ => hfac j]
  rw [Finset.prod_univ_sum]
  rfl

/-- **`(13)` in `d` dimensions.**  Every mode weight is at most `((N+1)^{-1} ρ/2π)^d`. -/
theorem norm_packetMode_le (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π) (c θ : Fin d → ℝ)
    (k : Fin d → ℕ × ℕ) :
    ‖packetMode N ρ c θ k‖ ≤ (((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d := by
  classical
  have hterm : ∀ j : Fin d,
      ‖((N : ℂ) + 1)⁻¹ * perFourierCoeff (perTent ρ) (((k j).1 : ℝ) - ((k j).2 : ℝ))
        * Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) * (θ j - c j) : ℝ) * Complex.I)‖
      ≤ ((N : ℝ) + 1)⁻¹ * (ρ / (2 * π)) := by
    intro j
    have hexp : ‖Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) * (θ j - c j) : ℝ)
        * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hinv : ‖((N : ℂ) + 1)⁻¹‖ = ((N : ℝ) + 1)⁻¹ := by
      rw [norm_inv]
      congr 1
      have : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [norm_mul, norm_mul, hexp, mul_one, hinv]
    exact mul_le_mul_of_nonneg_left (norm_perFourierCoeff_perTent_le hρ hρπ _) (by positivity)
  calc ‖packetMode N ρ c θ k‖
      = ∏ j, ‖((N : ℂ) + 1)⁻¹ * perFourierCoeff (perTent ρ) (((k j).1 : ℝ) - ((k j).2 : ℝ))
          * Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) * (θ j - c j) : ℝ) * Complex.I)‖ := by
        rw [packetMode, norm_prod]
    _ ≤ ∏ _j : Fin d, ((N : ℝ) + 1)⁻¹ * (ρ / (2 * π)) :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => hterm j
    _ = (((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The diagonal modes are the constant ones, and each equals `((N+1)^{-1} ρ/2π)^d`. -/
theorem packetMode_diagonal (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π) (c θ : Fin d → ℝ)
    {k : Fin d → ℕ × ℕ} (hk : ∀ j, (k j).1 = (k j).2) :
    packetMode N ρ c θ k = (((((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d : ℝ) : ℂ) := by
  classical
  have hterm : ∀ j : Fin d,
      ((N : ℂ) + 1)⁻¹ * perFourierCoeff (perTent ρ) (((k j).1 : ℝ) - ((k j).2 : ℝ))
        * Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) * (θ j - c j) : ℝ) * Complex.I)
      = ((((N : ℝ) + 1)⁻¹ * (ρ / (2 * π)) : ℝ) : ℂ) := by
    intro j
    have hzero : ((k j).1 : ℝ) - ((k j).2 : ℝ) = 0 := by rw [hk j]; ring
    rw [hzero, perFourierCoeff_perTent_zero hρ hρπ]
    have : ((0 : ℝ) * (θ j - c j) : ℝ) = 0 := by ring
    rw [this]
    push_cast
    simp
  rw [packetMode, Finset.prod_congr rfl fun j _ => hterm j, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  push_cast
  ring

/-- The diagonal pairs `(p,p)` with `p ≤ N`; these index the constant modes. -/
def diagPairs (N : ℕ) : Finset (ℕ × ℕ) := (Finset.range (N + 1)).image fun p => (p, p)

theorem card_diagPairs (N : ℕ) : (diagPairs N).card = N + 1 := by
  rw [diagPairs, Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.injEq _ _ _ _ ▸ hab).1),
    Finset.card_range]

theorem fst_eq_snd_of_mem_diagPairs {N : ℕ} {pq : ℕ × ℕ} (h : pq ∈ diagPairs N) : pq.1 = pq.2 := by
  rw [diagPairs, Finset.mem_image] at h
  obtain ⟨p, -, hp⟩ := h
  rw [← hp]

theorem diagPairs_subset (N : ℕ) :
    diagPairs N ⊆ Finset.range (N + 1) ×ˢ Finset.range (N + 1) := by
  intro pq h
  rw [diagPairs, Finset.mem_image] at h
  obtain ⟨p, hp, hpq⟩ := h
  rw [← hpq, Finset.mem_product]
  exact ⟨hp, hp⟩

/-- **`(11)` in `d` dimensions.**  The constant modes contribute exactly `μ_ρ = (ρ/2π)^d`. -/
theorem sum_diagonal_packetMode (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π) (c θ : Fin d → ℝ) :
    ∑ k ∈ Fintype.piFinset (fun _ : Fin d => diagPairs N), packetMode N ρ c θ k
      = (((ρ / (2 * π)) ^ d : ℝ) : ℂ) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hterm : ∀ k ∈ Fintype.piFinset (fun _ : Fin d => diagPairs N),
      packetMode N ρ c θ k = (((((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d : ℝ) : ℂ) := by
    intro k hk
    refine packetMode_diagonal N hρ hρπ c θ fun j => ?_
    exact fst_eq_snd_of_mem_diagPairs (Fintype.mem_piFinset.mp hk j)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Fintype.card_piFinset]
  have hcard : (∏ _j : Fin d, (diagPairs N).card) = (N + 1) ^ d := by
    rw [Finset.prod_congr rfl fun j _ => card_diagPairs N, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hcard, nsmul_eq_mul]
  have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
  push_cast
  rw [mul_pow, ← mul_assoc]
  rw [show ((N : ℂ) + 1) ^ d * (((N : ℂ) + 1)⁻¹) ^ d = 1 by
    rw [← mul_pow, mul_inv_cancel₀ (by
      have hR : ((N : ℝ) + 1) ≠ 0 := by positivity
      intro h
      exact hR (by exact_mod_cast h)), one_pow]]
  rw [one_mul]

/-- **The packet splits into its constant part `μ_ρ` and its nonconstant modes.** -/
theorem periodicProductFejerTent_eq_const_add (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π)
    (c θ : Fin d → ℝ) :
    ((periodicProductFejerTent N ρ c θ : ℝ) : ℂ)
      = (((ρ / (2 * π)) ^ d : ℝ) : ℂ)
        + ∑ k ∈ (Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
            \ Fintype.piFinset (fun _ : Fin d => diagPairs N), packetMode N ρ c θ k := by
  classical
  have hsub : Fintype.piFinset (fun _ : Fin d => diagPairs N)
      ⊆ Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1) :=
    Fintype.piFinset_subset _ _ fun _ => diagPairs_subset N
  rw [periodicProductFejerTent_eq_modeSum, ← Finset.sum_sdiff hsub,
    sum_diagonal_packetMode N hρ hρπ c θ]
  ring

/-! ### Evaluation along a frequency vector -/

/-- The frequency a mode carries along the direction `ω`. -/
def packetFreq (ω : Fin d → ℝ) (k : Fin d → ℕ × ℕ) : ℝ :=
  ∑ j, (((k j).1 : ℝ) - ((k j).2 : ℝ)) * ω j

/-- The time-independent amplitude of a mode. -/
def packetAmp (N : ℕ) (ρ : ℝ) (c : Fin d → ℝ) (k : Fin d → ℕ × ℕ) : ℂ :=
  ∏ j, (((N : ℂ) + 1)⁻¹ * perFourierCoeff (perTent ρ) (((k j).1 : ℝ) - ((k j).2 : ℝ))
    * Complex.exp ((-((((k j).1 : ℝ) - ((k j).2 : ℝ)) * c j) : ℝ) * Complex.I))

theorem norm_packetAmp_le (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π) (c : Fin d → ℝ)
    (k : Fin d → ℕ × ℕ) :
    ‖packetAmp N ρ c k‖ ≤ (((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d := by
  classical
  have hterm : ∀ j : Fin d,
      ‖((N : ℂ) + 1)⁻¹ * perFourierCoeff (perTent ρ) (((k j).1 : ℝ) - ((k j).2 : ℝ))
        * Complex.exp ((-((((k j).1 : ℝ) - ((k j).2 : ℝ)) * c j) : ℝ) * Complex.I)‖
      ≤ ((N : ℝ) + 1)⁻¹ * (ρ / (2 * π)) := by
    intro j
    have hexp : ‖Complex.exp ((-((((k j).1 : ℝ) - ((k j).2 : ℝ)) * c j) : ℝ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hinv : ‖((N : ℂ) + 1)⁻¹‖ = ((N : ℝ) + 1)⁻¹ := by
      rw [norm_inv]
      congr 1
      have : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [norm_mul, norm_mul, hexp, mul_one, hinv]
    exact mul_le_mul_of_nonneg_left (norm_perFourierCoeff_perTent_le hρ hρπ _) (by positivity)
  calc ‖packetAmp N ρ c k‖
      = ∏ j, ‖((N : ℂ) + 1)⁻¹ * perFourierCoeff (perTent ρ) (((k j).1 : ℝ) - ((k j).2 : ℝ))
          * Complex.exp ((-((((k j).1 : ℝ) - ((k j).2 : ℝ)) * c j) : ℝ) * Complex.I)‖ := by
        rw [packetAmp, norm_prod]
    _ ≤ ∏ _j : Fin d, ((N : ℝ) + 1)⁻¹ * (ρ / (2 * π)) :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => hterm j
    _ = (((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Each mode is a pure oscillation in time.**  Evaluated along `θ = tω`, a mode is its amplitude
times the character of the frequency it carries. -/
theorem packetMode_linearPhase (N : ℕ) (ρ : ℝ) (c ω : Fin d → ℝ) (k : Fin d → ℕ × ℕ) (t : ℝ) :
    packetMode N ρ c (fun j => t * ω j) k
      = packetAmp N ρ c k * Complex.exp ((t : ℂ) * (packetFreq ω k : ℂ) * Complex.I) := by
  classical
  have hchar : Complex.exp ((t : ℂ) * (packetFreq ω k : ℂ) * Complex.I)
      = ∏ j, Complex.exp ((((((k j).1 : ℝ) - ((k j).2 : ℝ)) * ω j * t : ℝ)) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    rw [packetFreq]
    push_cast
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  rw [packetAmp, hchar, ← Finset.prod_mul_distrib, packetMode]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hexp : Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) * (t * ω j - c j) : ℝ) * Complex.I)
      = Complex.exp ((-((((k j).1 : ℝ) - ((k j).2 : ℝ)) * c j) : ℝ) * Complex.I)
        * Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) * ω j * t : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- **`(18)` for the packet.**  Along a direction whose nonconstant modes all carry frequency at
least `βmin`, every moving window of length `T` sees the packet with mean at least `μ_ρ` minus the
aggregate oscillation error. -/
theorem window_mean_periodicProductFejerTent_ge (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π)
    (c ω : Fin d → ℝ) {βmin T : ℝ} (hβmin : 0 < βmin) (hT : 0 < T) (u : ℝ)
    (hsep : ∀ k ∈ (Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
        \ Fintype.piFinset (fun _ : Fin d => diagPairs N), βmin ≤ |packetFreq ω k|) :
    ((ρ / (2 * π)) ^ d : ℝ)
        - (((Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
            \ Fintype.piFinset (fun _ : Fin d => diagPairs N)).card : ℝ)
          * ((((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d) * (2 / (T * βmin))
      ≤ ((1 / (T : ℂ)) * ∫ t in u..(u + T),
          ((periodicProductFejerTent N ρ c (fun j => t * ω j) : ℝ) : ℂ)).re := by
  classical
  set S : Finset (Fin d → ℕ × ℕ) :=
    (Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
      \ Fintype.piFinset (fun _ : Fin d => diagPairs N) with hSdef
  have hpoint : ∀ t : ℝ, ((periodicProductFejerTent N ρ c (fun j => t * ω j) : ℝ) : ℂ)
      = (((ρ / (2 * π)) ^ d : ℝ) : ℂ)
        + ∑ i : {x // x ∈ S}, packetAmp N ρ c i.1
            * Complex.exp ((t : ℂ) * ((packetFreq ω i.1 : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [periodicProductFejerTent_eq_const_add N hρ hρπ, ← hSdef]
    congr 1
    rw [Finset.sum_coe_sort S (fun k => packetAmp N ρ c k
      * Complex.exp ((t : ℂ) * ((packetFreq ω k : ℝ) : ℂ) * Complex.I))]
    exact Finset.sum_congr rfl fun k _ => packetMode_linearPhase N ρ c ω k t
  have hmain := window_mean_ge (ι := {x // x ∈ S})
    (fun i => packetAmp N ρ c i.1) (fun i => packetFreq ω i.1) (μ := (ρ / (2 * π)) ^ d) hβmin
    (fun i => hsep i.1 i.2) ((((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d) (by positivity)
    (fun i => norm_packetAmp_le N hρ hρπ c i.1) hT u
  rw [Fintype.card_coe] at hmain
  refine le_trans hmain (le_of_eq ?_)
  congr 2
  exact intervalIntegral.integral_congr fun t _ => (hpoint t).symm

/-! ### The tent itself has the same window mean, up to the displacement -/

theorem continuous_fejerConv (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (hper : Function.Periodic f (2 * π)) : Continuous (fejerConv N f) := by
  have hC : Continuous fun θ : ℝ => ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
      ((N : ℂ) + 1)⁻¹ * perFourierCoeff f ((p : ℝ) - (q : ℝ))
        * Complex.exp (((((p : ℝ) - (q : ℝ)) * θ) : ℝ) * Complex.I) := by
    refine continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ => ?_
    fun_prop
  have heq : fejerConv N f = fun θ : ℝ =>
      (∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
        ((N : ℂ) + 1)⁻¹ * perFourierCoeff f ((p : ℝ) - (q : ℝ))
          * Complex.exp (((((p : ℝ) - (q : ℝ)) * θ) : ℝ) * Complex.I)).re := by
    funext θ
    rw [← fejerConv_eq_modeSum N hf hper θ, Complex.ofReal_re]
  rw [heq]
  exact Complex.continuous_re.comp hC

theorem continuous_periodicProductFejerTent (N : ℕ) (ρ : ℝ) (c ω : Fin d → ℝ) :
    Continuous fun t : ℝ => periodicProductFejerTent N ρ c (fun j => t * ω j) := by
  unfold periodicProductFejerTent
  refine continuous_finsetProd _ fun j _ => ?_
  exact (continuous_fejerConv N (continuous_perTent ρ) (periodic_perTent ρ)).comp (by fun_prop)

theorem continuous_periodicProductTent (ρ : ℝ) (c ω : Fin d → ℝ) :
    Continuous fun t : ℝ => periodicProductTent ρ c (fun j => t * ω j) := by
  unfold periodicProductTent
  refine continuous_finsetProd _ fun j _ => ?_
  exact (continuous_perTent ρ).comp (by fun_prop)

/-- The window mean of a real packet is the real part of its complex window mean. -/
theorem re_window_mean_ofReal {g : ℝ → ℝ} (hg : Continuous g) {T : ℝ} (hT : 0 < T) (u : ℝ) :
    ((1 / (T : ℂ)) * ∫ t in u..(u + T), ((g t : ℝ) : ℂ)).re
      = (1 / T) * ∫ t in u..(u + T), g t := by
  have hpush : (∫ t in u..(u + T), ((g t : ℝ) : ℂ)) = ((∫ t in u..(u + T), g t : ℝ) : ℂ) := by
    have h := Complex.ofRealCLM.intervalIntegral_comp_comm (f := g) (a := u) (b := u + T)
      (μ := MeasureTheory.volume) (hg.intervalIntegrable _ _)
    simp only [Complex.ofRealCLM_apply] at h
    exact h
  rw [hpush]
  have hTne : (T : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hT
  have : (1 / (T : ℂ)) * ((∫ t in u..(u + T), g t : ℝ) : ℂ)
      = (((1 / T) * ∫ t in u..(u + T), g t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, Complex.ofReal_re]

/-- **`(19)`.**  The tent itself inherits the window-mean floor, up to the uniform displacement
between it and its Fejér mean. -/
theorem window_mean_periodicProductTent_ge (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π)
    (c ω : Fin d → ℝ) {βmin T : ℝ} (hβmin : 0 < βmin) (hT : 0 < T) (u : ℝ)
    (hsep : ∀ k ∈ (Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
        \ Fintype.piFinset (fun _ : Fin d => diagPairs N), βmin ≤ |packetFreq ω k|) :
    ((ρ / (2 * π)) ^ d : ℝ)
        - (((Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
            \ Fintype.piFinset (fun _ : Fin d => diagPairs N)).card : ℝ)
          * ((((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d) * (2 / (T * βmin))
        - (d : ℝ) * ((1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1)))
      ≤ (1 / T) * ∫ t in u..(u + T), periodicProductTent ρ c (fun j => t * ω j) := by
  classical
  have hcontP : Continuous fun t : ℝ => periodicProductFejerTent N ρ c (fun j => t * ω j) :=
    continuous_periodicProductFejerTent N ρ c ω
  have hcontf : Continuous fun t : ℝ => periodicProductTent ρ c (fun j => t * ω j) :=
    continuous_periodicProductTent ρ c ω
  set D : ℝ := (d : ℝ) * ((1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1))) with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    positivity
  have hPmean := window_mean_periodicProductFejerTent_ge N hρ hρπ c ω hβmin hT u hsep
  rw [re_window_mean_ofReal hcontP hT u] at hPmean
  -- the two window means differ by at most the uniform displacement
  have hdiff : |(1 / T) * (∫ t in u..(u + T), periodicProductFejerTent N ρ c (fun j => t * ω j))
      - (1 / T) * (∫ t in u..(u + T), periodicProductTent ρ c (fun j => t * ω j))| ≤ D := by
    have hsub : (1 / T) * (∫ t in u..(u + T), periodicProductFejerTent N ρ c (fun j => t * ω j))
        - (1 / T) * (∫ t in u..(u + T), periodicProductTent ρ c (fun j => t * ω j))
        = (1 / T) * ∫ t in u..(u + T),
            (periodicProductFejerTent N ρ c (fun j => t * ω j)
              - periodicProductTent ρ c (fun j => t * ω j)) := by
      rw [intervalIntegral.integral_sub (hcontP.intervalIntegrable _ _)
        (hcontf.intervalIntegrable _ _)]
      ring
    have hpt : ∀ t ∈ Set.Icc u (u + T),
        |periodicProductFejerTent N ρ c (fun j => t * ω j)
          - periodicProductTent ρ c (fun j => t * ω j)| ≤ D :=
      fun t _ => abs_periodicProductFejerTent_sub_le N hρ c _
    have hbound : |(∫ t in u..(u + T),
        (periodicProductFejerTent N ρ c (fun j => t * ω j)
          - periodicProductTent ρ c (fun j => t * ω j)))| ≤ D * T := by
      have h := intervalIntegral.abs_integral_le_integral_abs (a := u) (b := u + T)
        (μ := MeasureTheory.volume)
        (f := fun t : ℝ => periodicProductFejerTent N ρ c (fun j => t * ω j)
          - periodicProductTent ρ c (fun j => t * ω j)) (by linarith)
      have h2 : (∫ t in u..(u + T),
          |periodicProductFejerTent N ρ c (fun j => t * ω j)
            - periodicProductTent ρ c (fun j => t * ω j)|) ≤ ∫ _t in u..(u + T), D := by
        refine intervalIntegral.integral_mono_on (by linarith)
          (((hcontP.sub hcontf).abs).intervalIntegrable _ _)
          (intervalIntegrable_const) hpt
      rw [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul, mul_comm] at h2
      linarith
    rw [hsub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / T)]
    calc (1 / T) * |(∫ t in u..(u + T),
          (periodicProductFejerTent N ρ c (fun j => t * ω j)
            - periodicProductTent ρ c (fun j => t * ω j)))|
        ≤ (1 / T) * (D * T) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = D := by field_simp
  have := abs_le.mp hdiff
  linarith [hPmean, this.1, this.2]

/-! ### The cube occupation of a moving window -/

/-- The times at which the orbit `t ↦ tω` lies in the open cube of half-width `ρ` around `c`. -/
def cubeVisit (ρ : ℝ) (c ω : Fin d → ℝ) : Set ℝ := {t | ∀ j, turnDist (t * ω j - c j) < ρ}

theorem measurableSet_cubeVisit (ρ : ℝ) (c ω : Fin d → ℝ) :
    MeasurableSet (cubeVisit ρ c ω) := by
  have hsplit : cubeVisit ρ c ω = ⋂ j : Fin d, {t : ℝ | turnDist (t * ω j - c j) < ρ} := by
    ext t
    simp [cubeVisit]
  rw [hsplit]
  refine MeasurableSet.iInter fun j => measurableSet_lt ?_ measurable_const
  exact (continuous_turnDist.comp (by fun_prop)).measurable

/-- The tent is bounded by the indicator of the cube it lives on. -/
theorem periodicProductTent_le_indicator {ρ : ℝ} (hρ : 0 < ρ) (c ω : Fin d → ℝ) (t : ℝ) :
    periodicProductTent ρ c (fun j => t * ω j)
      ≤ Set.indicator (cubeVisit ρ c ω) (fun _ => (1 : ℝ)) t := by
  classical
  by_cases ht : t ∈ cubeVisit ρ c ω
  · rw [Set.indicator_of_mem ht]
    refine Finset.prod_le_one (fun j _ => perTent_nonneg _ _) fun j _ => ?_
    exact perTent_le_one hρ _
  · rw [Set.indicator_of_notMem ht]
    rw [cubeVisit, Set.mem_setOf_eq] at ht
    push Not at ht
    obtain ⟨j, hj⟩ := ht
    have hzero : perTent ρ (t * ω j - c j) = 0 := by
      by_contra hne
      have hpos : 0 < perTent ρ (t * ω j - c j) :=
        lt_of_le_of_ne (perTent_nonneg _ _) (Ne.symm hne)
      exact absurd ((perTent_pos_iff hρ _).mp hpos) (not_lt.mpr hj)
    rw [periodicProductTent]
    exact le_of_eq (Finset.prod_eq_zero (Finset.mem_univ j) hzero)

/-- **`(5)`.**  The window mean of the tent is a lower bound for the fraction of the window spent
inside the cube. -/
theorem integral_le_measureReal_cubeVisit {ρ : ℝ} (hρ : 0 < ρ) (c ω : Fin d → ℝ) {T : ℝ}
    (hT : 0 < T) (u : ℝ) :
    (∫ t in u..(u + T), periodicProductTent ρ c (fun j => t * ω j))
      ≤ (MeasureTheory.volume (cubeVisit ρ c ω ∩ Set.Ioc u (u + T))).toReal := by
  classical
  have hle : u ≤ u + T := by linarith
  have hcontf : Continuous fun t : ℝ => periodicProductTent ρ c (fun j => t * ω j) :=
    continuous_periodicProductTent ρ c ω
  have hfin : MeasureTheory.volume (Set.Ioc u (u + T)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hIf : MeasureTheory.IntegrableOn
      (fun t : ℝ => periodicProductTent ρ c (fun j => t * ω j)) (Set.Ioc u (u + T)) :=
    (hcontf.intervalIntegrable u (u + T)).1
  have hIg : MeasureTheory.IntegrableOn
      (Set.indicator (cubeVisit ρ c ω) (fun _ => (1 : ℝ))) (Set.Ioc u (u + T)) :=
    (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hfin (by simp)).indicator
      (measurableSet_cubeVisit ρ c ω)
  have hmono : (∫ t in Set.Ioc u (u + T), periodicProductTent ρ c (fun j => t * ω j))
      ≤ ∫ t in Set.Ioc u (u + T), Set.indicator (cubeVisit ρ c ω) (fun _ => (1 : ℝ)) t :=
    MeasureTheory.setIntegral_mono_on hIf hIg measurableSet_Ioc
      fun t _ => periodicProductTent_le_indicator hρ c ω t
  have hind : (∫ t in Set.Ioc u (u + T), Set.indicator (cubeVisit ρ c ω) (fun _ => (1 : ℝ)) t)
      = (MeasureTheory.volume (Set.Ioc u (u + T) ∩ cubeVisit ρ c ω)).toReal := by
    rw [MeasureTheory.setIntegral_indicator (measurableSet_cubeVisit ρ c ω),
      MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    rfl
  rw [intervalIntegral.integral_of_le hle]
  rw [Set.inter_comm (cubeVisit ρ c ω) (Set.Ioc u (u + T))]
  rw [← hind]
  exact hmono

/-- **Theorem A's conclusion `(5)` in the form the card states it.**  Every moving window of length
`T` spends at least the displayed fraction of its length inside the cube. -/
theorem measureReal_cubeVisit_ge (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π)
    (c ω : Fin d → ℝ) {βmin T : ℝ} (hβmin : 0 < βmin) (hT : 0 < T) (u : ℝ)
    (hsep : ∀ k ∈ (Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
        \ Fintype.piFinset (fun _ : Fin d => diagPairs N), βmin ≤ |packetFreq ω k|) :
    (((ρ / (2 * π)) ^ d : ℝ)
        - (((Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
            \ Fintype.piFinset (fun _ : Fin d => diagPairs N)).card : ℝ)
          * ((((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d) * (2 / (T * βmin))
        - (d : ℝ) * ((1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1)))) * T
      ≤ (MeasureTheory.volume (cubeVisit ρ c ω ∩ Set.Ioc u (u + T))).toReal := by
  have hmean := window_mean_periodicProductTent_ge N hρ hρπ c ω hβmin hT u hsep
  have hvis := integral_le_measureReal_cubeVisit hρ c ω hT u
  have hTne : T ≠ 0 := ne_of_gt hT
  have hstep : ((ρ / (2 * π)) ^ d : ℝ)
      - (((Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
          \ Fintype.piFinset (fun _ : Fin d => diagPairs N)).card : ℝ)
        * ((((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d) * (2 / (T * βmin))
      - (d : ℝ) * ((1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1)))
      ≤ (1 / T) * (MeasureTheory.volume (cubeVisit ρ c ω ∩ Set.Ioc u (u + T))).toReal := by
    refine le_trans hmean ?_
    exact mul_le_mul_of_nonneg_left hvis (by positivity)
  have := mul_le_mul_of_nonneg_right hstep (le_of_lt hT)
  calc (((ρ / (2 * π)) ^ d : ℝ)
        - (((Fintype.piFinset fun _ : Fin d => Finset.range (N + 1) ×ˢ Finset.range (N + 1))
            \ Fintype.piFinset (fun _ : Fin d => diagPairs N)).card : ℝ)
          * ((((N : ℝ) + 1)⁻¹ * (ρ / (2 * π))) ^ d) * (2 / (T * βmin))
        - (d : ℝ) * ((1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1)))) * T
      ≤ (1 / T) * (MeasureTheory.volume (cubeVisit ρ c ω ∩ Set.Ioc u (u + T))).toReal * T := this
    _ = (MeasureTheory.volume (cubeVisit ρ c ω ∩ Set.Ioc u (u + T))).toReal := by
        field_simp

end ProductModes

end PeriodicFourier

end

end GaloisForLFunctions.HTGeometry
