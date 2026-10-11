import GaloisForLFunctions.RHTower.XiGaussianHeatHankelHeightHorizon
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelWindowCeiling
import GaloisForLFunctions.RHTower.XiCriticalZeroSeparatedNodes

/-!
# A polynomial height horizon for the heat Hankel ladder

The height horizon (`exists_height_heatHankel_re_pos`) says that for each degree `d` there is a
height `H(d)` such that the heat Hankel form is positive on all polynomials of degree `≤ d` at every
heat time once all off-line zeros lie above `H(d)`.  Its height came from an unquantified tail.  Here
it is made polynomial in `d`:

**Theorem** (`exists_poly_height_heatHankel_re_pos`).  There is `C ≥ 1` such that, for every `d`,
if every off-line zero `ρ = ½ + δ + iγ`, `δ ≠ 0`, has `|γ| > C (d + 1)^{63}`, then
`Re H_a(P, P) > 0` for every `a > 0` and every nonzero `P` of degree `≤ d`.  The same bound with
`d = N − 1` gives `Δ_M(a) > 0` for all `M ≤ N` and all `a > 0`
(`exists_poly_height_heatMomentDet_pos`).

Proof.
* The nodes are `d + 1` real zeros `t_i ∈ [1, 2 (K (d+1))^{63}]` with `|t_i − t_j| ≥ 1` from the Hardy
  census (`exists_separated_Xi_zeros`).  Their squares are `2`-separated, so Lagrange gives
  `coeffMass P ≤ (1 + Λ)^d Σ_i |P(t_i²)|` with `Λ = 4 (K (d+1))^{126}`.
* Small heat times `a (d + 1) ≤ κ` are the window.  For `a > κ/(d+1)` the nodes contribute
  `≥ e^{-aΛ} Σ |P(t_i²)|²`.  An off-line frequency `w` with `Re w ≥ Λ + Λ₂` contributes at most
  `coeffMass(P)² e^{-aΛ} η / (1 + |w|)` by `exp_mul_pow_le_of_level` at the explicit level
  `Λ₂ = B (d+1)^3` (`polyHorizon_level`).
* `η = 1/(2 (1+Λ)^{2d} (d+1) (S₁+1))` with `S₁ = Σ_q 1/(1 + |w_q|)` makes the off-line part less
  than the node part.
-/

open Complex Polynomial
open GaloisForLFunctions.HTGeometry (leadingMatrix coeffMass coeffMass_nonneg coeffMass_le_of_nodes)

namespace RHTower

noncomputable section

/-! ## The explicit level -/

/-- **The explicit level.**  For `κ > 0`, `K ≥ 1`, `S ≥ 0` there is `B > 0` such that for every `d`,
with `D = d + 1`, `Λ = 4 (K D)^{126}`, `Λ₂ = B D³` and
`η = 1 / (2 (1 + Λ)^{2d} D (S + 1))`:
`2d + 1 ≤ (κ/D)(1 + Λ₂)` and `(2d+1) log((Λ + 2)(1 + Λ₂)) + log(1/η) ≤ (κ/D) Λ₂`. -/
theorem polyHorizon_level {κ K S : ℝ} (hκ : 0 < κ) (hK : 1 ≤ K) (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 < B ∧ ∀ d : ℕ,
      ((2 * d + 1 : ℕ) : ℝ) ≤ κ / (d + 1) * (1 + B * (d + 1) ^ 3) ∧
      ((2 * d + 1 : ℕ) : ℝ) * Real.log ((4 * (K * (d + 1)) ^ 126 + 2) * (1 + B * (d + 1) ^ 3)) +
          Real.log (1 / (1 / (2 * (1 + 4 * (K * (d + 1)) ^ 126) ^ (2 * d) * (d + 1) * (S + 1)))) ≤
        κ / (d + 1) * (B * (d + 1) ^ 3) := by
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, L₀ = |Real.log (4 / κ)| := ⟨_, rfl⟩
  have hL₀0 : 0 ≤ L₀ := hL₀ ▸ abs_nonneg _
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 / κ * (27 + 504 * K + S + κ + 2 * L₀) := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  have hκB : κ * B = 2 * (27 + 504 * K + S + κ + 2 * L₀) := by rw [hB]; field_simp
  refine ⟨B, hB0, fun d => ?_⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = d + 1 := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := by rw [hD]; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hD0 : 0 < D := by linarith
  have hdD : (d : ℝ) ≤ D := by rw [hD]; linarith
  have h2d : ((2 * d + 1 : ℕ) : ℝ) ≤ 2 * D := by push_cast; linarith
  have hKD : 1 ≤ K * D := one_le_mul_of_one_le_of_one_le hK hD1
  rw [← hD]
  have hDD : D ≤ D ^ 2 := le_self_pow₀ hD1 (by norm_num)
  have hD3 : D ^ 3 = D * D ^ 2 := by ring
  have hdiv : κ / D * (B * D ^ 3) = κ * B * D ^ 2 := by field_simp
  constructor
  · -- `2d + 1 ≤ (κ/D)(1 + B D³)`
    have h1 : κ / D * (1 + B * D ^ 3) ≥ κ * B * D ^ 2 := by
      rw [mul_add, hdiv]
      have : 0 ≤ κ / D * 1 := by positivity
      linarith
    have h2 : 2 * D ≤ κ * B * D ^ 2 := by
      rw [hκB]
      have h54 : (2 : ℝ) ≤ 2 * (27 + 504 * K + S + κ + 2 * L₀) := by nlinarith
      nlinarith
    linarith
  · -- the logarithmic condition
    have hlogKD : Real.log (K * D) ≤ K * D := Real.log_le_self (by positivity)
    have hlogD : Real.log D ≤ D := Real.log_le_self hD0.le
    have hlog1 : Real.log (1 + 4 * (K * D) ^ 126) ≤ 4 + 126 * (K * D) := by
      have h5 : 1 + 4 * (K * D) ^ 126 ≤ 5 * (K * D) ^ 126 := by
        have : 1 ≤ (K * D) ^ 126 := one_le_pow₀ hKD
        linarith
      have hl5 : Real.log (5 : ℝ) ≤ 4 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5); linarith
      calc Real.log (1 + 4 * (K * D) ^ 126) ≤ Real.log (5 * (K * D) ^ 126) :=
            Real.log_le_log (by positivity) h5
        _ = Real.log 5 + 126 * Real.log (K * D) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
        _ ≤ 4 + 126 * (K * D) := by linarith
    have hlog2 : Real.log (4 * (K * D) ^ 126 + 2) ≤ 5 + 126 * (K * D) := by
      have h6 : 4 * (K * D) ^ 126 + 2 ≤ 6 * (K * D) ^ 126 := by
        have : 1 ≤ (K * D) ^ 126 := one_le_pow₀ hKD
        linarith
      have hl6 : Real.log (6 : ℝ) ≤ 5 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6); linarith
      calc Real.log (4 * (K * D) ^ 126 + 2) ≤ Real.log (6 * (K * D) ^ 126) :=
            Real.log_le_log (by positivity) h6
        _ = Real.log 6 + 126 * Real.log (K * D) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
        _ ≤ 5 + 126 * (K * D) := by linarith
    have hlog3 : Real.log (1 + B * D ^ 3) ≤ Real.log (1 + B) + 3 * D := by
      have h3 : 1 + B * D ^ 3 ≤ (1 + B) * D ^ 3 := by
        have : 1 ≤ D ^ 3 := one_le_pow₀ hD1
        nlinarith
      calc Real.log (1 + B * D ^ 3) ≤ Real.log ((1 + B) * D ^ 3) :=
            Real.log_le_log (by positivity) h3
        _ = Real.log (1 + B) + 3 * Real.log D := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
        _ ≤ Real.log (1 + B) + 3 * D := by linarith
    have hlogB : 2 * Real.log (1 + B) ≤ κ / 2 * (1 + B) + 2 * L₀ := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < κ / 4 * (1 + B))
      rw [Real.log_mul (by positivity) (by positivity)] at h
      have hl : -Real.log (κ / 4) ≤ L₀ := by
        rw [hL₀, show (4 : ℝ) / κ = (κ / 4)⁻¹ by field_simp, Real.log_inv, abs_neg]
        exact neg_le_abs _
      linarith
    have hlogS : Real.log (S + 1) ≤ S := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < S + 1); linarith
    have hlogη : Real.log (1 / (1 / (2 * (1 + 4 * (K * D) ^ 126) ^ (2 * d) * D * (S + 1)))) =
        Real.log 2 + (2 * d) * Real.log (1 + 4 * (K * D) ^ 126) + Real.log D +
          Real.log (S + 1) := by
      rw [one_div_one_div, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow]
      push_cast
      ring
    have hl2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    rw [hlogη, Real.log_mul (by positivity) (by positivity), hdiv]
    have hlogsum : 0 ≤ Real.log (4 * (K * D) ^ 126 + 2) + Real.log (1 + B * D ^ 3) := by
      have hp1 : 0 ≤ 4 * (K * D) ^ 126 := by positivity
      have hp2 : 0 ≤ B * D ^ 3 := by positivity
      have h1 : 0 ≤ Real.log (4 * (K * D) ^ 126 + 2) := Real.log_nonneg (by linarith)
      have h2 : 0 ≤ Real.log (1 + B * D ^ 3) := Real.log_nonneg (by linarith)
      linarith
    have hstep1 : ((2 * d + 1 : ℕ) : ℝ) * (Real.log (4 * (K * D) ^ 126 + 2) +
        Real.log (1 + B * D ^ 3)) ≤ 2 * D * ((5 + 126 * (K * D)) + (Real.log (1 + B) + 3 * D)) :=
      mul_le_mul h2d (by linarith) hlogsum (by positivity)
    have hlog10 : 0 ≤ Real.log (1 + 4 * (K * D) ^ 126) := Real.log_nonneg (by
      have : 0 ≤ 4 * (K * D) ^ 126 := by positivity
      linarith)
    have hstep2 : (2 * (d : ℝ)) * Real.log (1 + 4 * (K * D) ^ 126) ≤ 2 * D * (4 + 126 * (K * D)) :=
      mul_le_mul (by linarith) hlog1 hlog10 (by positivity)
    have hlogB0 : 0 ≤ Real.log (1 + B) := Real.log_nonneg (by linarith)
    have hDlogB : 2 * D * Real.log (1 + B) ≤ D ^ 2 * (κ / 2 * (1 + B) + 2 * L₀) := by
      have := mul_le_mul_of_nonneg_left hlogB hD0.le
      nlinarith
    have hSD : S ≤ S * D ^ 2 := le_mul_of_one_le_right hS (one_le_pow₀ hD1)
    have h1D : (1 : ℝ) ≤ D ^ 2 := one_le_pow₀ hD1
    have hκD : 0 ≤ κ * D ^ 2 := by positivity
    have hL₀D : 0 ≤ L₀ * D ^ 2 := by positivity
    have hκBD : κ * B * D ^ 2 = 2 * (27 + 504 * K + S + κ + 2 * L₀) * D ^ 2 := by rw [hκB]
    linarith [hstep1, hstep2, hl2, hlogD, hlogS, hDlogB, hκBD, hDD, h1D, hSD, hκD, hL₀D]

/-! ## Off-line terms above the level -/

/-- An off-line frequency above `Λ + Λ₂` contributes at most
`coeffMass(P)² e^{-aΛ} η / (1 + |w|)` at every heat time `a ≥ a₀`. -/
theorem norm_heatHankelTermAt_le_level {a a₀ Λ Λ₂ η : ℝ} {d : ℕ} {P : ℂ[X]} (haa : a₀ ≤ a) (hΛ0 : 0 ≤ Λ) (hΛ₂0 : 0 ≤ Λ₂) (hη0 : 0 < η) (hPd : P.natDegree ≤ d)
    (h1 : ((2 * d + 1 : ℕ) : ℝ) ≤ a₀ * (1 + Λ₂))
    (h2 : ((2 * d + 1 : ℕ) : ℝ) * Real.log ((Λ + 2) * (1 + Λ₂)) + Real.log (1 / η) ≤ a₀ * Λ₂)
    {q : XiZeroCopy} (hq : Λ + Λ₂ ≤ (xiHeatFrequency q).re) :
    ‖heatHankelTermAt a P P (xiHeatFrequency q)‖ ≤
      coeffMass P ^ 2 * Real.exp (-(a * Λ)) * η * (1 / (1 + ‖xiHeatFrequency q‖)) := by
  have hnorm := norm_heatHankelTermAt_le a P P q
  have hbase : 1 ≤ 1 + ‖xiHeatFrequency q‖ := by linarith [norm_nonneg (xiHeatFrequency q)]
  have hpow : (1 + ‖xiHeatFrequency q‖) ^ (P.natDegree + P.natDegree) ≤
      (1 + ‖xiHeatFrequency q‖) ^ (2 * d) := pow_le_pow_right₀ hbase (by omega)
  have hW0 : 0 ≤ (xiHeatFrequency q).re - Λ := by linarith
  have hexp : Real.exp (-(a * (xiHeatFrequency q).re)) ≤
      Real.exp (-(a * Λ)) * Real.exp (-(a₀ * ((xiHeatFrequency q).re - Λ))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hprod := mul_nonneg (sub_nonneg.2 haa) hW0
    linarith
  have hnw : ‖xiHeatFrequency q‖ ≤ (xiHeatFrequency q).re + 1 / 2 := norm_xiHeatFrequency_le_re q
  have hW' : Λ₂ ≤ (xiHeatFrequency q).re - Λ := by linarith
  have hlevel := exp_mul_pow_le_of_level (C := Λ + 2) (M := 2 * d + 1) (by positivity) hη0
    hΛ₂0 h1 h2 hW'
  have hbox : 1 + ‖xiHeatFrequency q‖ ≤ (Λ + 2) * (1 + ((xiHeatFrequency q).re - Λ)) := by
    have hprod := mul_nonneg (by linarith : (0 : ℝ) ≤ Λ + 1) hW0
    linarith
  have hn1 : 0 < 1 + ‖xiHeatFrequency q‖ := by positivity
  have hlev2 : Real.exp (-(a₀ * ((xiHeatFrequency q).re - Λ))) *
      (1 + ‖xiHeatFrequency q‖) ^ (2 * d) ≤ η * (1 / (1 + ‖xiHeatFrequency q‖)) := by
    rw [mul_one_div, le_div_iff₀ hn1]
    have hpow2 : (1 + ‖xiHeatFrequency q‖) ^ (2 * d + 1) ≤
        ((Λ + 2) * (1 + ((xiHeatFrequency q).re - Λ))) ^ (2 * d + 1) :=
      pow_le_pow_left₀ hn1.le hbox _
    calc Real.exp (-(a₀ * ((xiHeatFrequency q).re - Λ))) *
          (1 + ‖xiHeatFrequency q‖) ^ (2 * d) * (1 + ‖xiHeatFrequency q‖)
        = Real.exp (-(a₀ * ((xiHeatFrequency q).re - Λ))) *
            (1 + ‖xiHeatFrequency q‖) ^ (2 * d + 1) := by ring
      _ ≤ Real.exp (-(a₀ * ((xiHeatFrequency q).re - Λ))) *
            ((Λ + 2) * (1 + ((xiHeatFrequency q).re - Λ))) ^ (2 * d + 1) :=
          mul_le_mul_of_nonneg_left hpow2 (Real.exp_pos _).le
      _ ≤ η := hlevel
  have hmass : polyMass P = coeffMass P := rfl
  rw [hmass] at hnorm
  have hc := coeffMass_nonneg P
  have hstep : (1 + ‖xiHeatFrequency q‖) ^ (P.natDegree + P.natDegree) *
        Real.exp (-(a * (xiHeatFrequency q).re)) ≤
      (1 + ‖xiHeatFrequency q‖) ^ (2 * d) *
        (Real.exp (-(a * Λ)) * Real.exp (-(a₀ * ((xiHeatFrequency q).re - Λ)))) :=
    mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
  refine hnorm.trans ?_
  calc coeffMass P * coeffMass P * ((1 + ‖xiHeatFrequency q‖) ^ (P.natDegree + P.natDegree) *
        Real.exp (-(a * (xiHeatFrequency q).re)))
      ≤ coeffMass P * coeffMass P * ((1 + ‖xiHeatFrequency q‖) ^ (2 * d) *
        (Real.exp (-(a * Λ)) * Real.exp (-(a₀ * ((xiHeatFrequency q).re - Λ))))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = coeffMass P ^ 2 * Real.exp (-(a * Λ)) *
        (Real.exp (-(a₀ * ((xiHeatFrequency q).re - Λ))) * (1 + ‖xiHeatFrequency q‖) ^ (2 * d)) := by
        ring
    _ ≤ coeffMass P ^ 2 * Real.exp (-(a * Λ)) * (η * (1 / (1 + ‖xiHeatFrequency q‖))) :=
        mul_le_mul_of_nonneg_left hlev2 (by positivity)
    _ = coeffMass P ^ 2 * Real.exp (-(a * Λ)) * η * (1 / (1 + ‖xiHeatFrequency q‖)) := by ring

/-! ## Assembly from real nodes -/

/-- **Positivity from real nodes.**  Let `d + 1` distinct real frequencies `w_i ≤ Λ` control the
coefficient mass, `coeffMass P ≤ (1 + Λ)^d Σ_i |P(w_i)|`, and let every off-line term be at most
`coeffMass(P)² e^{-aΛ} η / (1 + |w|)` with `η = 1/(2 (1+Λ)^{2d} (d+1)(S₁+1))`.  Then
`Re H_a(P, P) > 0`. -/
theorem heatHankel_re_pos_of_nodes {a Λ η S₁ : ℝ} {d : ℕ} {P : ℂ[X]} (ha : 0 < a) (hP : P ≠ 0)
    (hS₁ : S₁ = ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖)) (hη0 : 0 < η)
    (hηval : η * (2 * (1 + Λ) ^ (2 * d) * (d + 1) * (S₁ + 1)) = 1) (hΛ0 : 0 ≤ Λ)
    (qn : Fin (d + 1) → XiZeroCopy) (hqinj : Function.Injective qn)
    (hqreal : ∀ i, (xiSpectralPoint (qn i)).im = 0)
    (hqΛ : ∀ i, (xiHeatFrequency (qn i)).re ≤ Λ)
    (hLag : coeffMass P ≤ (1 + Λ) ^ d * ∑ i, ‖P.eval (xiHeatFrequency (qn i))‖)
    (hoff : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 →
      ‖heatHankelTermAt a P P (xiHeatFrequency q)‖ ≤
        coeffMass P ^ 2 * Real.exp (-(a * Λ)) * η * (1 / (1 + ‖xiHeatFrequency q‖))) :
    0 < (heatHankel a P P).re := by
  classical
  have hS₁0 : 0 ≤ S₁ := hS₁ ▸ tsum_nonneg fun _ => by positivity
  obtain ⟨T, hT⟩ : ∃ T : XiZeroCopy → ℝ,
      ∀ q, T q = (heatHankelTermAt a P P (xiHeatFrequency q)).re := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : XiZeroCopy → ℝ, ∀ q, g q = 1 / (1 + ‖xiHeatFrequency q‖) :=
    ⟨_, fun _ => rfl⟩
  have hgs : Summable g := by
    rw [show g = fun q => 1 / (1 + ‖xiHeatFrequency q‖) from funext hg]
    exact summable_inv_one_add_norm_xiHeatFrequency
  have hg0 : ∀ q, 0 ≤ g q := fun q => by rw [hg]; positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = coeffMass P ^ 2 * Real.exp (-(a * Λ)) * η := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hTs : Summable T := by
    rw [show T = fun q => (heatHankelTermAt a P P (xiHeatFrequency q)).re from funext hT]
    exact (Complex.hasSum_re (summable_heatHankelTermAt ha P P).hasSum).summable
  obtain ⟨f, hf⟩ : ∃ f : XiZeroCopy → ℝ,
      ∀ q, f q = if (xiSpectralPoint q).im = 0 then 0 else g q := ⟨_, fun _ => rfl⟩
  have hf0 : ∀ q, 0 ≤ f q := fun q => by
    rw [hf]; split_ifs
    · exact le_rfl
    · exact hg0 q
  have hfle : ∀ q, f q ≤ g q := fun q => by
    rw [hf]; split_ifs
    · exact hg0 q
    · exact le_rfl
  have hfs : Summable f := hgs.of_nonneg_of_le hf0 hfle
  have hpt : ∀ q, 0 ≤ T q + M * f q := fun q => by
    by_cases hq : (xiSpectralPoint q).im = 0
    · have hw : (xiHeatFrequency q).im = 0 := by rw [xiHeatFrequency_im, hq, mul_zero]
      rw [hf, if_pos hq, mul_zero, add_zero, hT, re_heatHankelTermAt_of_im_eq_zero a P hw]
      positivity
    · rw [hf, if_neg hq]
      have hre : -‖heatHankelTermAt a P P (xiHeatFrequency q)‖ ≤ T q := by
        rw [hT]; exact neg_le_of_abs_le (Complex.abs_re_le_norm _)
      have hle := hoff q hq
      rw [← hg, ← hM] at hle
      linarith
  have hlow := (hTs.add (hfs.mul_left M)).sum_le_tsum (Finset.univ.image qn) fun q _ => hpt q
  rw [Summable.tsum_add hTs (hfs.mul_left M), tsum_mul_left] at hlow
  have hinj : Set.InjOn qn ↑(Finset.univ : Finset (Fin (d + 1))) := fun i _ j _ hij => hqinj hij
  rw [Finset.sum_image hinj] at hlow
  have hnode : ∀ i : Fin (d + 1), Real.exp (-(a * Λ)) * ‖P.eval (xiHeatFrequency (qn i))‖ ^ 2 ≤
      T (qn i) + M * f (qn i) := by
    intro i
    have hw : (xiHeatFrequency (qn i)).im = 0 := by
      rw [xiHeatFrequency_im, hqreal i, mul_zero]
    rw [hf, if_pos (hqreal i), mul_zero, add_zero, hT, re_heatHankelTermAt_of_im_eq_zero a P hw]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
    have := hqΛ i
    nlinarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = ∑ i : Fin (d + 1), ‖P.eval (xiHeatFrequency (qn i))‖ ^ 2 :=
    ⟨_, rfl⟩
  have hnodes' : Real.exp (-(a * Λ)) * σ ≤ ∑' q, T q + M * ∑' q, f q := by
    rw [hσ, Finset.mul_sum]
    exact (Finset.sum_le_sum fun i _ => hnode i).trans hlow
  have hBS : ∑' q, f q ≤ S₁ := by
    rw [hS₁]
    refine hfs.tsum_le_tsum (fun q => (hfle q).trans_eq (hg q)) ?_
    exact summable_inv_one_add_norm_xiHeatFrequency
  have hmassσ : coeffMass P ^ 2 ≤ (1 + Λ) ^ (2 * d) * (d + 1) * σ := by
    have h2s : (∑ i : Fin (d + 1), ‖P.eval (xiHeatFrequency (qn i))‖) ^ 2 ≤ (d + 1) * σ := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (d + 1))))
        (f := fun i => ‖P.eval (xiHeatFrequency (qn i))‖)
      rw [hσ]
      simpa [Finset.card_univ, Fintype.card_fin] using this
    have hc := coeffMass_nonneg P
    calc coeffMass P ^ 2 ≤ ((1 + Λ) ^ d * ∑ i, ‖P.eval (xiHeatFrequency (qn i))‖) ^ 2 :=
          pow_le_pow_left₀ hc hLag 2
      _ = (1 + Λ) ^ (2 * d) * (∑ i, ‖P.eval (xiHeatFrequency (qn i))‖) ^ 2 := by ring
      _ ≤ (1 + Λ) ^ (2 * d) * ((d + 1) * σ) :=
          mul_le_mul_of_nonneg_left h2s (by positivity)
      _ = (1 + Λ) ^ (2 * d) * (d + 1) * σ := by ring
  have hcpos := coeffMass_pos hP
  have hσpos : 0 < σ := by
    by_contra hσ0
    push Not at hσ0
    have : (1 + Λ) ^ (2 * d) * (d + 1) * σ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hσ0
    nlinarith [sq_pos_of_pos hcpos]
  have hexpΛ := Real.exp_pos (-(a * Λ))
  have hMS : M * ∑' q, f q ≤ Real.exp (-(a * Λ)) * σ / 2 := by
    have h1' : M * ∑' q, f q ≤ M * S₁ := mul_le_mul_of_nonneg_left hBS hM0
    have hMS1 : M * S₁ ≤ Real.exp (-(a * Λ)) * ((1 + Λ) ^ (2 * d) * (d + 1) * σ) * η * S₁ := by
      rw [hM]
      have := mul_le_mul_of_nonneg_right hmassσ
        (by positivity : (0 : ℝ) ≤ Real.exp (-(a * Λ)) * η * S₁)
      linarith
    have key : (1 + Λ) ^ (2 * d) * (d + 1) * η * S₁ ≤ 1 / 2 := by
      have h' : (1 + Λ) ^ (2 * d) * (d + 1) * η * (2 * (S₁ + 1)) = 1 := by
        linear_combination hηval
      have hpos : 0 ≤ (1 + Λ) ^ (2 * d) * (d + 1) * η := by positivity
      nlinarith
    have hfin : Real.exp (-(a * Λ)) * ((1 + Λ) ^ (2 * d) * (d + 1) * σ) * η * S₁ ≤
        Real.exp (-(a * Λ)) * σ / 2 := by
      have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ Real.exp (-(a * Λ)) * σ)
      linarith
    linarith
  have hHre : (heatHankel a P P).re = ∑' q, T q := by
    rw [heatHankel, Complex.re_tsum (summable_heatHankelTermAt ha P P)]
    exact tsum_congr fun q => (hT q).symm
  rw [hHre]
  nlinarith [mul_pos hexpΛ hσpos]

/-! ## Positivity from separated real zeros above a level -/

/-- **Positivity from separated real zeros.**  Let `t_0, …, t_d` be real zeros of `Ξ` with
`t_i ≥ 1`, `|t_i − t_j| ≥ 1` and `t_i² ≤ Λ`.  Suppose every off-line frequency has
`Re w ≥ Λ + Λ₂` or is killed by `P` (`P(w) = 0` or `P(w̄) = 0`), where `Λ₂` satisfies the level
conditions at `a₀ ≤ a` for
`η = 1/(2 (1+Λ)^{2d} (d+1)(S₁+1))`.  Then `Re H_a(P, P) > 0` for every nonzero `P` of degree `≤ d`. -/
theorem heatHankel_re_pos_of_separated_zeros_of_vanish {a a₀ Λ Λ₂ η S₁ : ℝ} {d : ℕ} {P : ℂ[X]} (ha : 0 < a)
    (hP : P ≠ 0) (hPd : P.natDegree ≤ d) (haa : a₀ ≤ a) (hΛ0 : 0 ≤ Λ) (hΛ₂0 : 0 ≤ Λ₂)
    (hS₁ : S₁ = ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖)) (hη0 : 0 < η)
    (hηval : η * (2 * (1 + Λ) ^ (2 * d) * (d + 1) * (S₁ + 1)) = 1)
    (h1 : ((2 * d + 1 : ℕ) : ℝ) ≤ a₀ * (1 + Λ₂))
    (h2 : ((2 * d + 1 : ℕ) : ℝ) * Real.log ((Λ + 2) * (1 + Λ₂)) + Real.log (1 / η) ≤ a₀ * Λ₂)
    (t : Fin (d + 1) → ℝ) (hXi : ∀ i, Xi (t i) = 0) (ht1 : ∀ i, 1 ≤ t i)
    (htΛ : ∀ i, t i ^ 2 ≤ Λ) (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (hoff : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → Λ + Λ₂ ≤ (xiHeatFrequency q).re ∨
      P.eval (xiHeatFrequency q) = 0 ∨ P.eval ((starRingEnd ℂ) (xiHeatFrequency q)) = 0) :
    0 < (heatHankel a P P).re := by
  classical
  have hcopy : ∀ i, ∃ q : XiZeroCopy, xiSpectralPoint q = (t i : ℂ) := fun i => by
    obtain ⟨q, hq, -⟩ := exists_xiZeroCopy_im_eq_of_Xi_eq_zero (hXi i)
    exact ⟨q, hq⟩
  choose qn hqn using hcopy
  have hwn : ∀ i, xiHeatFrequency (qn i) = ((t i ^ 2 : ℝ) : ℂ) := fun i => by
    rw [xiHeatFrequency, hqn]; push_cast; ring
  have hqinj : Function.Injective qn := fun i j h => by
    by_contra hij
    have hs := hsep i j hij
    have hq := congrArg xiSpectralPoint h
    rw [hqn, hqn, Complex.ofReal_inj] at hq
    rw [hq, sub_self, abs_zero] at hs
    linarith
  have htnR : ∀ i, ‖xiHeatFrequency (qn i)‖ ≤ Λ := fun i => by
    rw [hwn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (t i))]
    exact htΛ i
  have htnsep : ∀ i j, i ≠ j →
      (1 : ℝ) ≤ ‖xiHeatFrequency (qn i) - xiHeatFrequency (qn j)‖ := fun i j hij => by
    rw [hwn, hwn, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hs := hsep i j hij
    have hi := ht1 i
    have hj := ht1 j
    rw [show t i ^ 2 - t j ^ 2 = (t i - t j) * (t i + t j) by ring, abs_mul,
      abs_of_pos (by linarith : 0 < t i + t j)]
    nlinarith
  have hLag := coeffMass_le_of_nodes (fun i => xiHeatFrequency (qn i)) one_pos htnR htnsep P hPd
  rw [div_one] at hLag
  exact heatHankel_re_pos_of_nodes ha hP hS₁ hη0 hηval hΛ0 qn hqinj
    (fun i => by rw [hqn, ofReal_im]) (fun i => by rw [hwn, ofReal_re]; exact htΛ i) hLag
    fun q hq => by
      rcases hoff q hq with hlev | hvan
      · exact norm_heatHankelTermAt_le_level haa hΛ0 hΛ₂0 hη0 hPd h1 h2 hlev
      · have h0 : heatHankelTermAt a P P (xiHeatFrequency q) = 0 := by
          rcases hvan with hv | hv <;> simp [heatHankelTermAt, hv]
        rw [h0, norm_zero]
        positivity

/-- **Positivity from separated real zeros**, with every off-line frequency above the level. -/
theorem heatHankel_re_pos_of_separated_zeros {a a₀ Λ Λ₂ η S₁ : ℝ} {d : ℕ} {P : ℂ[X]} (ha : 0 < a)
    (hP : P ≠ 0) (hPd : P.natDegree ≤ d) (haa : a₀ ≤ a) (hΛ0 : 0 ≤ Λ) (hΛ₂0 : 0 ≤ Λ₂)
    (hS₁ : S₁ = ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖)) (hη0 : 0 < η)
    (hηval : η * (2 * (1 + Λ) ^ (2 * d) * (d + 1) * (S₁ + 1)) = 1)
    (h1 : ((2 * d + 1 : ℕ) : ℝ) ≤ a₀ * (1 + Λ₂))
    (h2 : ((2 * d + 1 : ℕ) : ℝ) * Real.log ((Λ + 2) * (1 + Λ₂)) + Real.log (1 / η) ≤ a₀ * Λ₂)
    (t : Fin (d + 1) → ℝ) (hXi : ∀ i, Xi (t i) = 0) (ht1 : ∀ i, 1 ≤ t i)
    (htΛ : ∀ i, t i ^ 2 ≤ Λ) (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|)
    (hoff : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → Λ + Λ₂ ≤ (xiHeatFrequency q).re) :
    0 < (heatHankel a P P).re :=
  heatHankel_re_pos_of_separated_zeros_of_vanish ha hP hPd haa hΛ0 hΛ₂0 hS₁ hη0 hηval h1 h2 t hXi
    ht1 htΛ hsep fun q hq => Or.inl (hoff q hq)

/-! ## The polynomial horizon -/

/-- **Polynomial height horizon.**  There is `C ≥ 1` such that for every `d`, if every off-line zero
has height `> C (d + 1)^{63}`, the heat Hankel form is positive on every nonzero polynomial of
degree `≤ d` at every heat time. -/
theorem exists_poly_height_heatHankel_re_pos :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ,
      (∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → C * (d + 1) ^ 63 < |(xiSpectralPoint q).re|) →
      ∀ a : ℝ, 0 < a → ∀ P : ℂ[X], P ≠ 0 → P.natDegree ≤ d → 0 < (heatHankel a P P).re := by
  classical
  obtain ⟨K, hK1, hnodes⟩ := exists_separated_Xi_zeros
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = routeUCompletedPrimeGammaAperture := ⟨_, rfl⟩
  have hκ0 : 0 < κ := hκdef ▸ routeUCompletedPrimeGammaAperture_pos
  obtain ⟨S₁, hS₁⟩ : ∃ S, S = ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) := ⟨_, rfl⟩
  have hS₁0 : 0 ≤ S₁ := hS₁ ▸ tsum_nonneg fun _ => by positivity
  obtain ⟨B, hB0, hlev⟩ := polyHorizon_level hκ0 hK1 hS₁0
  refine ⟨Real.sqrt (4 * K ^ 126 + B + 2), ?_, fun d hhigh a ha P hP hPd => ?_⟩
  · rw [Real.le_sqrt (by norm_num) (by positivity)]
    have : 0 ≤ 4 * K ^ 126 := by positivity
    linarith
  -- the window
  rcases le_or_gt (a * (d + 1)) κ with hwin | hwin
  · refine heatHankel_re_pos_of_window ha hP (le_trans ?_ (hκdef ▸ hwin))
    have : (P.natDegree : ℝ) ≤ d := by exact_mod_cast hPd
    nlinarith
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = κ / (d + 1) := ⟨_, rfl⟩
  have ha₀0 : 0 < a₀ := by rw [ha₀]; positivity
  have haa : a₀ ≤ a := by rw [ha₀, div_le_iff₀ hd1]; linarith
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = 4 * (K * (d + 1)) ^ 126 := ⟨_, rfl⟩
  obtain ⟨Λ₂, hΛ₂⟩ : ∃ Λ₂ : ℝ, Λ₂ = B * (d + 1) ^ 3 := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (2 * (1 + Λ) ^ (2 * d) * (d + 1) * (S₁ + 1)) := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hΛ₂0 : 0 ≤ Λ₂ := by rw [hΛ₂]; positivity
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηval : η * (2 * (1 + Λ) ^ (2 * d) * (d + 1) * (S₁ + 1)) = 1 := by
    rw [hη]; field_simp
  obtain ⟨h1, h2⟩ := hlev d
  rw [← hΛ₂, ← ha₀] at h1
  rw [← hΛ, ← hΛ₂, ← ha₀, ← hη] at h2
  -- off-line frequencies lie above `Λ + Λ₂`
  have hoff : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 →
      Λ + Λ₂ ≤ (xiHeatFrequency q).re := by
    intro q hq
    have hH := hhigh q hq
    have hsq : (Real.sqrt (4 * K ^ 126 + B + 2) * (d + 1) ^ 63) ^ 2 =
        (4 * K ^ 126 + B + 2) * (d + 1) ^ 126 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul]
    have hpos : 0 ≤ Real.sqrt (4 * K ^ 126 + B + 2) * (d + 1) ^ 63 := by positivity
    have hre2 : (Real.sqrt (4 * K ^ 126 + B + 2) * (d + 1) ^ 63) ^ 2 ≤
        (xiSpectralPoint q).re ^ 2 := by
      rw [← sq_abs (xiSpectralPoint q).re]
      exact pow_le_pow_left₀ hpos hH.le 2
    have hd126 : (d + 1 : ℝ) ^ 3 ≤ (d + 1) ^ 126 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have h1d : (1 : ℝ) ≤ (d + 1) ^ 126 := one_le_pow₀ (by linarith)
    have him := xiSpectralPoint_im_sq_lt_quarter q
    rw [xiHeatFrequency_re, hΛ, hΛ₂]
    have hKd : (K * (d + 1)) ^ 126 = K ^ 126 * (d + 1) ^ 126 := mul_pow _ _ _
    rw [hsq] at hre2
    have hB3 : B * (d + 1) ^ 3 ≤ B * (d + 1) ^ 126 := mul_le_mul_of_nonneg_left hd126 hB0.le
    generalize ((d : ℝ) + 1) = D at hre2 hd126 h1d hB3 hKd ⊢
    rw [hKd]
    linarith
  -- the nodes
  obtain ⟨t, hXi, ht1, htle, hsep⟩ := hnodes d
  have htΛ : ∀ i, t i ^ 2 ≤ Λ := fun i => by
    have h0 : 0 ≤ t i := by linarith [ht1 i]
    calc t i ^ 2 ≤ (2 * (K * (d + 1)) ^ 63) ^ 2 := pow_le_pow_left₀ h0 (htle i) 2
      _ = Λ := by rw [hΛ, mul_pow, ← pow_mul]; norm_num
  exact heatHankel_re_pos_of_separated_zeros ha hP hPd haa hΛ0 hΛ₂0 hS₁ hη0 hηval h1 h2 t hXi ht1
    htΛ hsep hoff

/-- **Polynomial height horizon for the determinants.**  There is `C ≥ 1` such that for every rank
`N`, if every off-line zero has height `> C N^{63}`, then `Δ_M(a) > 0` for all `M ≤ N` and all
`a > 0`. -/
theorem exists_poly_height_heatMomentDet_pos :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ,
      (∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → C * (N + 1) ^ 63 < |(xiSpectralPoint q).re|) →
      ∀ M ≤ N, ∀ a : ℝ, 0 < a → 0 < (leadingMatrix (heatMomentArray a) M).det := by
  obtain ⟨C, hC1, hC⟩ := exists_poly_height_heatHankel_re_pos
  refine ⟨C, hC1, fun N hhigh M hMN a ha => ?_⟩
  refine heatMomentDet_pos_of_forall ha fun P hP0 hdeg => ?_
  exact hC N hhigh a ha P hP0 (by omega)

end

end RHTower
