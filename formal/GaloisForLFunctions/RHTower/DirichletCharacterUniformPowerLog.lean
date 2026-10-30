import GaloisForLFunctions.RHTower.DirichletCharacterUniformPerron
import GaloisForLFunctions.RHTower.PerronPolyExpAbsorb

/-!
# Uniform signed character tent decay on growing conductor families

All moduli bounded by a fixed power of the logarithm share one decay rate and
one starting horizon. A narrowed contour balances the left displacement with
the two right-line tails; its constants retain the conductor cost explicitly.
-/

noncomputable section

set_option autoImplicit false

namespace RHTower

open MeasureTheory Set Filter ArithmeticFunction
open _root_.Complex

private theorem exists_uniform_character_tent_exp_pow_bound {A : ℝ} (hA : 0 ≤ A) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 ≤ C ∧ ∀ u : ℝ, 6 ≤ u →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ u ^ (10 * A) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖∑' n : ℕ, (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
              ((max (Real.log (Real.exp (u ^ (10 : ℕ)) / n)) 0 : ℝ) : ℂ)‖ ≤
            C * Real.exp (u ^ (10 : ℕ)) * Real.exp (-(κ * u)) := by
  let ε := 1 / (10 * A + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨c₀, B₀, hc₀, hB₀, hc₀8, hmaster⟩ := exists_conductor_uniform_character_perron_bound hε
  let R := 10 * A + 3
  have hR1 : 1 ≤ R := by dsimp only [R]; linarith only [hA]
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  let c := c₀ / R ^ 2
  let B := B₀ * R ^ 3
  have hc : 0 < c := div_pos hc₀ (sq_pos_of_pos hR0)
  have hB : 0 < B := mul_pos hB₀ (pow_pos hR0 _)
  have hc8 : c ≤ 1 / 8 := (div_le_self hc₀.le (one_le_pow₀ hR1)).trans hc₀8
  let D := 1 + c
  let k := c / D ^ (9 : ℕ)
  let d := min 1 k
  let Ct := 32 * D ^ (18 : ℕ) / c ^ (2 : ℕ)
  let Cv := 2 * Real.pi * B * D ^ (9 : ℕ)
  let Ch := 16 * B * c
  let C₀ := (2 * Real.pi)⁻¹ * (Ct + Cv + Ch)
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
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨d / 2, C₀ * ((Nat.factorial 18 : ℝ) * (2 / d) ^ (18 : ℕ)), by positivity,
    by positivity, fun u hu q _ hq χ hχ => ?_⟩
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
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    have hδc : δ ≤ c := div_le_self hc.le (one_le_pow₀ (hu1.trans
      (le_mul_of_one_le_left hu0.le hD1)))
    exact (hδc.trans hc8).trans (by norm_num)
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
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hqe0 : 0 < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hq0 _
  have heexp : 10 * A * ε ≤ 1 := by
    dsimp only [ε]
    rw [mul_one_div, div_le_iff₀ (show 0 < 10 * A + 1 by linarith only [hA])]
    linarith only [hA]
  have hqe : (q : ℝ) ^ ε ≤ u := by
    calc
      _ ≤ (u ^ (10 * A)) ^ ε := Real.rpow_le_rpow hq0.le hq hε.le
      _ = u ^ (10 * A * ε) := (Real.rpow_mul hu0.le _ _).symm
      _ ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 heexp
      _ = u := Real.rpow_one _
  have hqlog : Real.log (q : ℝ) ≤ 10 * A * u := by
    calc
      _ ≤ Real.log (u ^ (10 * A)) := Real.log_le_log hq0 hq
      _ = (10 * A) * Real.log u := Real.log_rpow hu0 _
      _ ≤ 10 * A * u := mul_le_mul_of_nonneg_left
        ((Real.log_le_sub_one_of_pos hu0).trans (by linarith)) (by positivity)
  let L := Real.log ((q : ℝ) * (T + 5))
  have hL1 : 1 ≤ L := by
    have h := one_le_log_conductor (q := q) (T + 2)
    simpa only [abs_of_pos (show 0 < T + 2 by linarith only [hT]),
      show T + 2 + 3 = T + 5 by ring] using h
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hD2 : D ≤ 2 := by dsimp only [D]; linarith only [hc8]
  have hlogT5 : Real.log (T + 5) ≤ 3 * u := by
    have hT5 : T + 5 ≤ 3 * Real.exp (D * u) := by
      dsimp only [T]
      linarith only [hexp6]
    have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
      simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    calc
      _ ≤ Real.log (3 * Real.exp (D * u)) :=
        Real.log_le_log (by linarith only [hT]) hT5
      _ = Real.log 3 + D * u := by rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
      _ ≤ 3 * u := by
        have hDu2 := mul_le_mul_of_nonneg_right hD2 hu0.le
        linarith only [hlog3, hDu2, hu]
  have hL : L ≤ R * u := by
    dsimp only [L]
    rw [Real.log_mul hq0.ne' (by linarith only [hT] : T + 5 ≠ 0)]
    dsimp only [R]
    linarith only [hqlog, hlogT5]
  have huDu : u ≤ D * u := le_mul_of_one_le_left hu0.le hD1
  have hpow39 : u ^ (3 : ℕ) ≤ (D * u) ^ (9 : ℕ) := by
    calc
      _ ≤ u ^ (3 : ℕ) * u ^ (6 : ℕ) :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hu1)
      _ = u ^ (9 : ℕ) := by ring
      _ ≤ (D * u) ^ (9 : ℕ) := pow_le_pow_left₀ hu0.le huDu 9
  have hδ3 : δ ≤ c / u ^ (3 : ℕ) :=
    div_le_div_of_nonneg_left hc.le (pow_pos hu0 _) hpow39
  have hwidth : δ ≤ c₀ * (q : ℝ) ^ (-ε) / L ^ 2 := by
    rw [Real.rpow_neg hq0.le, ← div_eq_mul_inv, div_div]
    apply (le_div_iff₀ (mul_pos hqe0 (sq_pos_of_pos hL0))).mpr
    calc
      δ * ((q : ℝ) ^ ε * L ^ 2) ≤ δ * (u * (R * u) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hqe (pow_le_pow_left₀ hL0.le hL 2) (sq_nonneg _) hu0.le) hδ.le
      _ ≤ (c / u ^ (3 : ℕ)) * (u * (R * u) ^ 2) :=
        mul_le_mul_of_nonneg_right hδ3 (by positivity)
      _ = c₀ := by dsimp only [c]; field_simp [hu0.ne', hR0.ne']
  let M₀ := B₀ * (q : ℝ) ^ ε * L ^ 3
  have hMb : M₀ ≤ M := by
    have hpow49 : u ^ (4 : ℕ) ≤ (D * u) ^ (9 : ℕ) := by
      calc
        _ ≤ u ^ (4 : ℕ) * u ^ (5 : ℕ) :=
          le_mul_of_one_le_right (by positivity) (one_le_pow₀ hu1)
        _ = u ^ (9 : ℕ) := by ring
        _ ≤ (D * u) ^ (9 : ℕ) := pow_le_pow_left₀ hu0.le huDu 9
    calc
      M₀ ≤ B₀ * u * (R * u) ^ 3 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hqe hB₀.le)
          (pow_le_pow_left₀ hL0.le hL 3) (by positivity) (by positivity)
      _ = B * u ^ (4 : ℕ) := by dsimp only [B]; ring
      _ ≤ M := mul_le_mul_of_nonneg_left hpow49 hB.le
  have hm₀ := hmaster q χ hχ x T δ hx1 hT hδ hwidth
  change _ ≤ (2 * Real.pi)⁻¹ *
    (2 * ((8 / δ ^ (2 : ℕ) * x ^ (1 + δ)) / T) + M₀ * x ^ (1 - δ) * (Real.pi / (1 - δ)) +
      2 * (M₀ * x ^ (1 + δ) / T ^ (2 : ℕ) * (2 * δ))) at hm₀
  have hvM : M₀ * x ^ (1 - δ) * (Real.pi / (1 - δ)) ≤
      M * x ^ (1 - δ) * (Real.pi / (1 - δ)) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMb (by positivity)) (by positivity)
  have hhM : 2 * (M₀ * x ^ (1 + δ) / T ^ (2 : ℕ) * (2 * δ)) ≤
      2 * (M * x ^ (1 + δ) / T ^ (2 : ℕ) * (2 * δ)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hMb (by positivity)) (sq_nonneg T))
        (by positivity)) (by norm_num)
  have hm := hm₀.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hvM) hhM) (by positivity))
  have hfull : ‖∑' n : ℕ, (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
        ((max (Real.log (x / n)) 0 : ℝ) : ℂ)‖ ≤ C₀ * G := by
    apply hm.trans
    calc
      _ ≤ (2 * Real.pi)⁻¹ * (Ct * G + Cv * G + Ch * G) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add htail hvert) hhoriz) (by positivity)
      _ = C₀ * G := by dsimp only [C₀]; ring
  have habs := pow_mul_exp_neg_le_absorb_half hd hu0.le 18
  have hscale := mul_le_mul_of_nonneg_left habs (show 0 ≤ C₀ * x by positivity)
  apply hfull.trans
  dsimp only [G, x] at hscale ⊢
  rw [show d / 2 * u = d * u / 2 from by ring]
  convert hscale using 1 <;> ac_rfl

/-- One rate and one horizon control every nonprincipal character whose modulus
is bounded by a fixed power of the physical logarithm. -/
theorem exists_conductor_uniform_character_tent_power_log {A : ℝ} (hA : 0 ≤ A) :
    ∃ κ C x₀ : ℝ, 0 < κ ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖∑' n : ℕ, (χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) *
              ((max (Real.log (x / n)) 0 : ℝ) : ℂ)‖ ≤
            C * x * Real.exp (-(κ * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨κ, C, hκ, hC, hbound⟩ := exists_uniform_character_tent_exp_pow_bound hA
  refine ⟨κ, C, max 3 (Real.exp ((6 : ℝ) ^ (10 : ℕ))), hκ, hC, le_max_left _ _, fun x hx q _ hq χ hχ => ?_⟩
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
  have hqu : (q : ℝ) ≤ u ^ (10 * A) := by
    calc
      _ ≤ Real.log x ^ A := hq
      _ = (u ^ (10 : ℕ)) ^ A := by rw [hu10]
      _ = u ^ (10 * A) := by rw [← Real.rpow_natCast u 10, ← Real.rpow_mul hu.le]; norm_num
  have h := hbound u hu6 q hqu χ hχ
  rwa [hu10, Real.exp_log hx0] at h


#print axioms exists_conductor_uniform_character_tent_power_log

end RHTower
