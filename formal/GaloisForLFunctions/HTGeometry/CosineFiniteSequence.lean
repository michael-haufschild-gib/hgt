import GaloisForLFunctions.HTGeometry.CosineFiniteCorner
import GaloisForLFunctions.HTGeometry.CosineTwoPoleSequence
import GaloisForLFunctions.HTGeometry.PolyExpDecayLimit

/-! # Exact finite-coordinate sequence and its vanishing, nonzero correction

Only the qualitative polynomial-exponential limit is used from PolyExpDecayLimit.
Exact local factorization gives a correction tending to zero. Its factors
are eventually nonzero. The source points escape all finite sets through
the scaled limit 27, with no error or magnitude estimate.
-/

namespace GaloisForLFunctions.HTGeometry.CosineFiniteSequence

open Complex Filter LabeledCosineDescent
open CosineTwoPoleCorner (small)
open CosineFiniteCorner
open scoped Topology

noncomputable section

theorem exponential_parameter_eq (m n : ℕ) :
    (parameters m n).2 = (Real.exp (-((2 * Real.pi / (m : ℝ)) * (n : ℝ))) : ℂ) := by
  rw [Complex.ofReal_exp]
  dsimp [parameters]
  congr 1
  push_cast
  ring

theorem exponential_parameter_limit (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n => (parameters m n).2) atTop (𝓝 0) := by
  have hk : 0 < 2 * Real.pi / (m : ℝ) :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) (by exact_mod_cast hm)
  have h := (tendsto_pow_mul_exp_neg_scaled 0 hk).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  simpa [Function.comp_def, exponential_parameter_eq] using hc

theorem scaled_exponential_parameter_limit (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => (n : ℂ) * (parameters m n).2) atTop (𝓝 0) := by
  have hk : 0 < 2 * Real.pi / (m : ℝ) :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) (by exact_mod_cast hm)
  have h := (tendsto_pow_mul_exp_neg_scaled 1 hk).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  simpa [Function.comp_def, exponential_parameter_eq] using hc

theorem parameters_limit (m : ℕ) (hm : 0 < m) :
    Tendsto (parameters m) atTop (𝓝 (0, 0)) :=
  CosineCornerSequence.inverse_parameter_limit.prodMk_nhds (exponential_parameter_limit m hm)

def smallSequence (m : ℕ) (ell : ℂ × ℂ → ℂ) (n : ℕ) : ℂ :=
  small (parameters m n, ell (parameters m n))

theorem smallSequence_ne_zero (m n : ℕ) (ell : ℂ × ℂ → ℂ) : smallSequence m ell n ≠ 0 :=
  mul_ne_zero (exp_ne_zero _) (exp_ne_zero _)

theorem smallSequence_limit {m : ℕ} (hm : 0 < m) {ell : ℂ × ℂ → ℂ}
    (hell : AnalyticAt ℂ ell (0, 0)) : Tendsto (smallSequence m ell) atTop (𝓝 0) := by
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    (hell.continuousAt.tendsto.comp (parameters_limit m hm))
  change Tendsto (fun n => (parameters m n).2 * exp (ell (parameters m n))) atTop (𝓝 0)
  convert! (exponential_parameter_limit m hm).mul he using 1
  simp only [zero_mul]

theorem scaled_smallSequence_limit {m : ℕ} (hm : 0 < m) {ell : ℂ × ℂ → ℂ}
    (hell : AnalyticAt ℂ ell (0, 0)) :
    Tendsto (fun n : ℕ => (n : ℂ) * smallSequence m ell n) atTop (𝓝 0) := by
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    (hell.continuousAt.tendsto.comp (parameters_limit m hm))
  simpa [smallSequence, small, mul_assoc] using (scaled_exponential_parameter_limit m hm).mul he

theorem scaled_germ_displacement_limit {u H : ℂ → ℂ} {k : ℕ}
    (hH : AnalyticAt ℂ H 0) (hk : 0 < k)
    (hfact : ∀ᶠ z in 𝓝 (0 : ℂ), u z - u 0 = z ^ k * H z)
    {v : ℕ → ℂ} (hv : Tendsto v atTop (𝓝 0))
    (hnv : Tendsto (fun n : ℕ => (n : ℂ) * v n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℂ) * (u (v n) - u 0)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => ((n : ℂ) * v n) * v n ^ (k - 1) * H (v n))
      atTop (𝓝 0) := by
    simpa using (hnv.mul (hv.pow (k - 1))).mul (hH.continuousAt.tendsto.comp hv)
  apply hlim.congr'
  filter_upwards [hv.eventually hfact] with n hn
  have hexp : v n ^ k = v n * v n ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [hn, hexp]
  ring

def correction (u : ℂ → ℂ) (s : ℕ → ℂ) (n : ℕ) : ℂ :=
  27 / (4 * (Real.pi : ℂ) ^ 2) * (u (s n) - u 0) *
    (4 * Real.pi * n + u (s n) + u 0)

theorem correction_limit {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) {s : ℕ → ℂ}
    (hs : Tendsto s atTop (𝓝 0))
    (hflat : Tendsto (fun n : ℕ => (n : ℂ) * (u (s n) - u 0)) atTop (𝓝 0)) :
    Tendsto (correction u s) atTop (𝓝 0) := by
  have hulim := hu.continuousAt.tendsto.comp hs
  have hdiff : Tendsto (fun n => u (s n) - u 0) atTop (𝓝 0) := by
    simpa using hulim.sub_const (u 0)
  have hlim := ((hflat.const_mul (4 * (Real.pi : ℂ))).add
    (hdiff.mul (hulim.add_const (u 0)))).const_mul (27 / (4 * (Real.pi : ℂ) ^ 2))
  simp only [mul_zero, zero_mul, add_zero] at hlim
  apply hlim.congr
  intro n
  dsimp [correction]
  ring

theorem point_decomposition (u : ℂ → ℂ) (s : ℕ → ℂ) (n : ℕ) :
    squareCoordinate ((n : ℂ) * (2 * Real.pi) + u (s n)) =
      27 * (n : ℂ) ^ 2 + (27 * u 0 / Real.pi) * n +
        (27 * u 0 ^ 2 / (4 * (Real.pi : ℂ) ^ 2) - 1 / 12) + correction u s n := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  dsimp [squareCoordinate, correction]
  field_simp
  ring

theorem correction_eventually_ne_zero {u H : ℂ → ℂ} {k : ℕ}
    (hu : AnalyticAt ℂ u 0) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 ≠ 0)
    (hfact : ∀ᶠ z in 𝓝 (0 : ℂ), u z - u 0 = z ^ k * H z)
    {s : ℕ → ℂ} (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0) :
    ∀ᶠ n in atTop, correction u s n ≠ 0 := by
  have hu' := hu.continuousAt.tendsto.comp hs
  have hscale : Tendsto (fun n : ℕ => 4 * (Real.pi : ℂ) +
      (n : ℂ)⁻¹ * (u (s n) + u 0)) atTop (𝓝 (4 * (Real.pi : ℂ))) := by
    simpa using tendsto_const_nhds.add
      (CosineCornerSequence.inverse_parameter_limit.mul (hu'.add_const (u 0)))
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4p : 4 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hp
  filter_upwards [hscale.eventually_ne h4p, hs.eventually hfact,
    hs.eventually (hH.continuousAt.eventually_ne hH0), eventually_gt_atTop (0 : ℕ)]
    with n hn hfn hHn hn0
  have hlast : 4 * (Real.pi : ℂ) * n + u (s n) + u 0 ≠ 0 := by
    intro hz
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn0
    apply hn
    calc
      _ = (n : ℂ)⁻¹ * (4 * Real.pi * n + u (s n) + u 0) := by field_simp; ring
      _ = 0 := by rw [hz, mul_zero]
  exact mul_ne_zero (mul_ne_zero
    (div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp)))
    (by rw [hfn]; exact mul_ne_zero (pow_ne_zero k (hs0 n)) hHn)) hlast

theorem point_scaled_limit {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) {s : ℕ → ℂ}
    (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℂ)⁻¹ ^ 2 *
      squareCoordinate ((n : ℂ) * (2 * Real.pi) + u (s n))) atTop (𝓝 27) := by
  have hi := CosineCornerSequence.inverse_parameter_limit
  have hu' := hu.continuousAt.tendsto.comp hs
  have hU : Tendsto (fun n : ℕ => (n : ℂ)⁻¹ * ((n : ℂ) * (2 * Real.pi) + u (s n)))
      atTop (𝓝 (2 * (Real.pi : ℂ))) := by
    have hl : Tendsto (fun n : ℕ => 2 * (Real.pi : ℂ) + (n : ℂ)⁻¹ * u (s n))
        atTop (𝓝 (2 * (Real.pi : ℂ))) := by
      simpa using tendsto_const_nhds.add (hi.mul hu')
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
    simp only [mul_add, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  have hlim := ((hU.pow 2).const_mul 27 |>.div_const (4 * (Real.pi : ℂ) ^ 2)).sub
    ((hi.pow 2).div_const 12)
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hv : 27 * (2 * (Real.pi : ℂ)) ^ 2 / (4 * (Real.pi : ℂ) ^ 2) - 0 ^ 2 / 12 = 27 := by
    field_simp
    ring
  rw [hv] at hlim
  simpa only [CosineTwoPoleSequence.scaled_squareCoordinate] using hlim

end

end GaloisForLFunctions.HTGeometry.CosineFiniteSequence
