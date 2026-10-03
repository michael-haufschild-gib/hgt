import GaloisForLFunctions.RHTower.DirichletCharacterPerronBounds
import GaloisForLFunctions.RHTower.PerronPolyExpAbsorb

/-!
# Actual quantitative character tent-sum decay

The complete character Perron contour estimate gives a power-log exponential
rate for every nonprincipal character. The height exp((1+c)*u)-3 uses the proved
strip constant c directly. Both tails and both horizontal edges remain in the
estimate before polynomial absorption; u=(log x)^(1/10).

This is a signed complex tent-sum rate. Recovering the unsmoothed character
prime sum additionally requires the short-interval defect estimate.
-/

noncomputable section
namespace RHTower
open MeasureTheory Set Filter ArithmeticFunction Complex
variable {Q : ℕ} [NeZero Q]

private theorem exists_smoothed_character_exp_pow_bound
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 ≤ C ∧ ∀ u : ℝ, 6 ≤ u →
      ‖∑' n : ℕ, (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
          ((max (Real.log (Real.exp (u ^ (10 : ℕ)) / n)) 0 : ℝ) : ℂ)‖ ≤
        C * Real.exp (u ^ (10 : ℕ)) * Real.exp (-(κ * u)) := by
  obtain ⟨c, B, hc, hB, hcA, hmaster⟩ := exists_smoothed_character_vonMangoldt_contour_bound hχ
  let D := 1 + c
  let k := c / D ^ (9 : ℕ)
  let d := min 1 k
  let Ct := 32 * D ^ (18 : ℕ) / c ^ (2 : ℕ)
  let Cv := 2 * Real.pi * B * D ^ (9 : ℕ)
  let Ch := 16 * B * c
  let A := (2 * Real.pi)⁻¹ * (Ct + Cv + Ch)
  have hD1 : 1 ≤ D := by dsimp only [D]; linarith only [hc]
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hk : 0 < k := div_pos hc (pow_pos hD _)
  have hkc : k ≤ c := div_le_self hc.le (one_le_pow₀ hD1)
  have hd : 0 < d := lt_min zero_lt_one hk
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdk : d ≤ k := min_le_right _ _
  have hCt : 0 ≤ Ct := by dsimp [Ct]; positivity
  have hCv : 0 ≤ Cv := by dsimp [Cv]; positivity
  have hCh : 0 ≤ Ch := by dsimp [Ch]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨d / 2, A * ((Nat.factorial 18 : ℝ) * (2 / d) ^ (18 : ℕ)), by positivity,
    by positivity, fun u hu => ?_⟩
  have hu0 : 0 < u := by linarith only [hu]
  have hu1 : 1 ≤ u := by linarith only [hu]
  let x := Real.exp (u ^ (10 : ℕ))
  let T := Real.exp (D * u) - 3
  let δ := c / (D * u) ^ (9 : ℕ)
  let M := B * (D * u) ^ (9 : ℕ)
  have hx : 0 < x := Real.exp_pos _
  have hx1 : 1 ≤ x := Real.one_le_exp (by positivity)
  have hDu : 6 ≤ D * u := (show (6 : ℝ) ≤ u from hu).trans (le_mul_of_one_le_left hu0.le hD1)
  have hexp6 : 6 ≤ Real.exp (D * u) := by linarith only [hDu, Real.add_one_le_exp (D * u)]
  have hT : 0 < T := by dsimp only [T]; linarith only [hexp6]
  have hThalf : Real.exp (D * u) / 2 ≤ T := by dsimp only [T]; linarith only [hexp6]
  have hlogT : Real.log (3 + T) = D * u := by
    dsimp [T]
    rw [show 3 + (Real.exp (D * u) - 3) = Real.exp (D * u) from by ring, Real.log_exp]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < (D * u) ^ (9 : ℕ))).mpr
    have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hlogs : Real.log 3 ≤ Real.log (3 + T) := Real.log_le_log (by norm_num) (by linarith only [hT])
    rw [hlogT] at hlogs
    have hp := pow_le_pow_left₀ hlog3.le hlogs 9
    linarith only [hcA, hp]
  have hδu : u ^ (10 : ℕ) * δ = k * u := by
    dsimp only [δ, k]
    field_simp [hD.ne', hu0.ne']
  have hxa : x ^ (1 + δ) = x * Real.exp (k * u) := by
    rw [Real.rpow_def_of_pos hx]
    change Real.exp (Real.log (Real.exp (u ^ (10 : ℕ))) * (1 + δ)) = _
    rw [Real.log_exp, show u ^ (10 : ℕ) * (1 + δ) = u ^ (10 : ℕ) + k * u from by rw [mul_add, mul_one, hδu],
      Real.exp_add]
  have hxb : x ^ (1 - δ) = x * Real.exp (-(k * u)) := by
    rw [Real.rpow_def_of_pos hx]
    change Real.exp (Real.log (Real.exp (u ^ (10 : ℕ))) * (1 - δ)) = _
    rw [Real.log_exp, show u ^ (10 : ℕ) * (1 - δ) = u ^ (10 : ℕ) + -(k * u) from by rw [mul_sub, mul_one, hδu]; ring,
      Real.exp_add]
  have hTinv : 1 / T ≤ 2 * Real.exp (-(D * u)) := by
    calc
      1 / T ≤ 1 / (Real.exp (D * u) / 2) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity) hThalf
      _ = 2 * Real.exp (-(D * u)) := by rw [Real.exp_neg]; field_simp
  have hTinv2 : (1 / T) ^ (2 : ℕ) ≤ 4 * Real.exp (-(2 * D * u)) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / T) hTinv 2
    have he : (2 * Real.exp (-(D * u))) ^ (2 : ℕ) = 4 * Real.exp (-(2 * D * u)) := by
      rw [mul_pow, show (2 : ℝ) ^ (2 : ℕ) = 4 from by norm_num, pow_two (Real.exp _), ← Real.exp_add]
      congr 1
      congr 1
      ring
    rwa [he] at h
  have hdecay1 : Real.exp (-((D - k) * u)) ≤ Real.exp (-(d * u)) := by
    apply Real.exp_le_exp.mpr
    have hDk : 1 ≤ D - k := by dsimp only [D]; linarith only [hkc]
    exact neg_le_neg (mul_le_mul_of_nonneg_right (hd1.trans hDk) hu0.le)
  have hdecay2 : Real.exp (-((2 * D - k) * u)) ≤ Real.exp (-(d * u)) := by
    apply Real.exp_le_exp.mpr
    have hDk : 1 ≤ 2 * D - k := by dsimp only [D]; linarith only [hkc, hc]
    exact neg_le_neg (mul_le_mul_of_nonneg_right (hd1.trans hDk) hu0.le)
  have hdecayk : Real.exp (-(k * u)) ≤ Real.exp (-(d * u)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hdk hu0.le))
  have hquot : x ^ (1 + δ) / T ≤ 2 * x * Real.exp (-((D - k) * u)) := by
    rw [hxa, div_eq_mul_inv]
    have h := mul_le_mul_of_nonneg_left hTinv (show 0 ≤ x * Real.exp (k * u) by positivity)
    calc
      _ = (x * Real.exp (k * u)) * (1 / T) := by ring
      _ ≤ (x * Real.exp (k * u)) * (2 * Real.exp (-(D * u))) := h
      _ = _ := by
        rw [show (x * Real.exp (k * u)) * (2 * Real.exp (-(D * u))) =
          2 * x * (Real.exp (k * u) * Real.exp (-(D * u))) from by ring,
          ← Real.exp_add]
        congr 1
        congr 1
        ring
  have hquot2 : x ^ (1 + δ) / T ^ (2 : ℕ) ≤
      4 * x * Real.exp (-((2 * D - k) * u)) := by
    rw [hxa]
    calc
      _ = (x * Real.exp (k * u)) * (1 / T) ^ (2 : ℕ) := by ring
      _ ≤ (x * Real.exp (k * u)) * (4 * Real.exp (-(2 * D * u))) :=
        mul_le_mul_of_nonneg_left hTinv2 (by positivity)
      _ = _ := by
        rw [show (x * Real.exp (k * u)) * (4 * Real.exp (-(2 * D * u))) =
          4 * x * (Real.exp (k * u) * Real.exp (-(2 * D * u))) from by ring,
          ← Real.exp_add]
        congr 1
        congr 1
        ring
  have hu9 : 1 ≤ u ^ (9 : ℕ) := one_le_pow₀ hu1
  have hu18 : 1 ≤ u ^ (18 : ℕ) := one_le_pow₀ hu1
  have hpow : u ^ (9 : ℕ) ≤ u ^ (18 : ℕ) := by
    have he : u ^ (18 : ℕ) = (u ^ (9 : ℕ)) ^ (2 : ℕ) := by ring
    rw [he]
    nlinarith only [hu9]
  let G := u ^ (18 : ℕ) * x * Real.exp (-(d * u))
  have htail : 2 * ((8 / δ ^ (2 : ℕ) * x ^ (1 + δ)) / T) ≤ Ct * G := by
    calc
      _ = (16 / δ ^ (2 : ℕ)) * (x ^ (1 + δ) / T) := by ring
      _ ≤ (16 / δ ^ (2 : ℕ)) * (2 * x * Real.exp (-((D - k) * u))) :=
        mul_le_mul_of_nonneg_left hquot (by positivity)
      _ ≤ (16 / δ ^ (2 : ℕ)) * (2 * x * Real.exp (-(d * u))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdecay1 (by positivity)) (by positivity)
      _ = Ct * G := by
        dsimp only [δ, Ct, G]
        field_simp [hc.ne', hD.ne', hu0.ne']
        ring
  have hb : 0 < 1 - δ := by linarith only [hδhalf]
  have hpi : Real.pi / (1 - δ) ≤ 2 * Real.pi := by
    apply (div_le_iff₀ hb).mpr
    nlinarith only [Real.pi_pos, hδhalf]
  have hvert : M * x ^ (1 - δ) * (Real.pi / (1 - δ)) ≤ Cv * G := by
    rw [hxb]
    calc
      _ ≤ M * (x * Real.exp (-(k * u))) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_left hpi (by positivity)
      _ = Cv * (u ^ (9 : ℕ) * x * Real.exp (-(k * u))) := by dsimp only [M, Cv]; ring
      _ ≤ Cv * G := by
        apply mul_le_mul_of_nonneg_left _ hCv
        exact mul_le_mul (mul_le_mul_of_nonneg_right hpow hx.le) hdecayk (by positivity) (by positivity)
  have hhoriz : 2 * (M * x ^ (1 + δ) / T ^ (2 : ℕ) * (2 * δ)) ≤ Ch * G := by
    calc
      _ = (4 * B * c) * (x ^ (1 + δ) / T ^ (2 : ℕ)) := by
        dsimp only [M, δ]
        field_simp [hD.ne', hu0.ne']
        ring
      _ ≤ (4 * B * c) * (4 * x * Real.exp (-((2 * D - k) * u))) :=
        mul_le_mul_of_nonneg_left hquot2 (by positivity)
      _ ≤ (4 * B * c) * (4 * x * Real.exp (-(d * u))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdecay2 (by positivity)) (by positivity)
      _ = Ch * (x * Real.exp (-(d * u))) := by dsimp only [Ch]; ring
      _ ≤ Ch * G := by
        apply mul_le_mul_of_nonneg_left _ hCh
        dsimp only [G]
        calc
          _ ≤ u ^ (18 : ℕ) * (x * Real.exp (-(d * u))) :=
            le_mul_of_one_le_left (by positivity) hu18
          _ = _ := by ring
  have hm := hmaster x T hx1 hT
  rw [hlogT] at hm
  change _ ≤ (2 * Real.pi)⁻¹ *
    (2 * ((8 / δ ^ (2 : ℕ) * x ^ (1 + δ)) / T) + M * x ^ (1 - δ) * (Real.pi / (1 - δ)) +
      2 * (M * x ^ (1 + δ) / T ^ (2 : ℕ) * (2 * δ))) at hm
  have hfull : ‖∑' n : ℕ, (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
        ((max (Real.log (x / n)) 0 : ℝ) : ℂ)‖ ≤ A * G := by
    apply hm.trans
    calc
      _ ≤ (2 * Real.pi)⁻¹ * (Ct * G + Cv * G + Ch * G) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add htail hvert) hhoriz) (by positivity)
      _ = A * G := by dsimp only [A]; ring
  have habs := pow_mul_exp_neg_le_absorb_half hd hu0.le 18
  have hscale := mul_le_mul_of_nonneg_left habs (show 0 ≤ A * x by positivity)
  apply hfull.trans
  dsimp only [G, x] at hscale ⊢
  rw [show d / 2 * u = d * u / 2 from by ring]
  convert hscale using 1 <;> ac_rfl

/-- An actual quantitative signed tent-sum rate for every nonprincipal character,
with all contour errors accounted for and no analytic hypothesis. -/
theorem exists_smoothed_character_vonMangoldt_power_log
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ κ C x₀ : ℝ, 0 < κ ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ‖∑' n : ℕ, (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
          ((max (Real.log (x / n)) 0 : ℝ) : ℂ)‖ ≤
        C * x * Real.exp (-(κ * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨κ, C, hκ, hC, hbound⟩ := exists_smoothed_character_exp_pow_bound hχ
  refine ⟨κ, C, max 3 (Real.exp ((6 : ℝ) ^ (10 : ℕ))), hκ, hC, le_max_left _ _, fun x hx => ?_⟩
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  let u := Real.log x ^ ((1 : ℝ) / 10)
  have hu : 0 < u := Real.rpow_pos_of_pos hlogx _
  have hu10 : u ^ (10 : ℕ) = Real.log x := by
    dsimp only [u]
    rw [← Real.rpow_natCast (Real.log x ^ ((1 : ℝ) / 10)) 10, ← Real.rpow_mul hlogx.le]
    norm_num
  have hu6 : 6 ≤ u := by
    have h := Real.log_le_log (Real.exp_pos ((6 : ℝ) ^ (10 : ℕ))) ((le_max_right _ _).trans hx)
    rw [Real.log_exp, ← hu10] at h
    exact le_of_pow_le_pow_left₀ (by norm_num) hu.le h
  have h := hbound u hu6
  rwa [hu10, Real.exp_log hx0] at h

end RHTower
