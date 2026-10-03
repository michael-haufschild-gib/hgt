import GaloisForLFunctions.RHTower.DirichletCharacterPerron
import GaloisForLFunctions.RHTower.PerronUnsmoothingStep
import GaloisForLFunctions.RHTower.DirichletCharacterPowerLog
import GaloisForLFunctions.RHTower.ChebyshevPsiPowerLogPNT

/-!
# Quantitative unsmoothing for actual character sums

A positive scalar tent-kernel defect controls the signed complex error. The proved
character tent decay and ordinary Chebyshev rate then give an actual unsmoothed
character von Mangoldt estimate, without an assumed character prime-sum bound.
-/

noncomputable section
namespace RHTower
open MeasureTheory Set Filter ArithmeticFunction Complex
variable {Q : ℕ} [NeZero Q]

/-- Actual signed character tent sum. -/
def characterPerronTentSum (χ : DirichletCharacter ℂ Q) (x : ℝ) : ℂ :=
  ∑' n : ℕ, χ n * ((ArithmeticFunction.vonMangoldt n * max (Real.log (x / n)) 0 : ℝ) : ℂ)

/-- Actual character-twisted Chebyshev sum, retaining complex coefficients. -/
def characterChebyshevPsi (χ : DirichletCharacter ℂ Q) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)

omit [NeZero Q] in
private theorem summable_character_mul_real (χ : DirichletCharacter ℂ Q)
    {f : ℕ → ℝ} (hf : Summable f) : Summable (fun n : ℕ => χ n * (f n : ℂ)) := by
  apply hf.abs.of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (χ.norm_le_one _)

omit [NeZero Q] in
/-- The signed unsmoothing defect is dominated by ordinary von Mangoldt mass in the
short interval. No monotonicity of the complex character sum is assumed. -/
theorem norm_characterPerron_unsmoothing_defect (χ : DirichletCharacter ℂ Q)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖characterPerronTentSum χ y - characterPerronTentSum χ x -
      (Real.log (y / x) : ℂ) * characterChebyshevPsi χ ⌊x⌋₊‖ ≤
        Real.log (y / x) * (chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊) := by
  have hy : 0 < y := hx.trans_le hxy
  let h := Real.log (y / x)
  let g : ℕ → ℝ := fun n => if n ∈ Finset.Icc 1 ⌊x⌋₊ then ArithmeticFunction.vonMangoldt n * h else 0
  let f : ℝ → ℕ → ℝ := fun t n => ArithmeticFunction.vonMangoldt n * max (Real.log (t / n)) 0
  let D : ℕ → ℝ := fun n => f y n - f x n - g n
  have hxsum : Summable (f x) := summable_perronTent hx
  have hysum : Summable (f y) := summable_perronTent hy
  have hgsum : Summable g := summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊)
    (fun n hn => if_neg hn)
  have hDsum : Summable D := (hysum.sub hxsum).sub hgsum
  have hDpos : ∀ n : ℕ, 0 ≤ D n := by
    intro n
    by_cases hn : n ∈ Finset.Icc 1 ⌊x⌋₊
    · have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
      have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hx.le)
      have hny : (n : ℝ) ≤ y := hnx.trans hxy
      have hlogx : 0 ≤ Real.log (x / n) := Real.log_nonneg ((one_le_div hn0).mpr hnx)
      have hlogy : 0 ≤ Real.log (y / n) := Real.log_nonneg ((one_le_div hn0).mpr hny)
      have hdiff : Real.log (y / n) - Real.log (x / n) = h := by
        rw [← Real.log_div (by positivity) (by positivity)]
        dsimp only [h]
        congr 1
        field_simp
      dsimp only [D, f, g]
      rw [if_pos hn, max_eq_left hlogx, max_eq_left hlogy]
      have he : ArithmeticFunction.vonMangoldt n * Real.log (y / n) -
          ArithmeticFunction.vonMangoldt n * Real.log (x / n) - ArithmeticFunction.vonMangoldt n * h = 0 := by
        rw [← mul_sub, hdiff]
        ring
      rw [he]
    · dsimp only [D, f, g]
      rw [if_neg hn, sub_zero]
      apply sub_nonneg.mpr
      apply mul_le_mul_of_nonneg_left _ (vonMangoldt_nonneg (n := n))
      apply max_le_max _ le_rfl
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · simp
      · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
        exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hxy hn0.le)
  have hgscalar : ∑' n : ℕ, g n = h * chebyshevPsi ⌊x⌋₊ := by
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => if_neg hn), chebyshevPsi, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos hn]
    ring
  have hgchar : ∑' n : ℕ, χ n * (g n : ℂ) = (h : ℂ) * characterChebyshevPsi χ ⌊x⌋₊ := by
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => by simp only [g, if_neg hn, Complex.ofReal_zero, mul_zero]),
      characterChebyshevPsi, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [g, if_pos hn, Complex.ofReal_mul]
    ring
  have hxchar := summable_character_mul_real χ hxsum
  have hychar := summable_character_mul_real χ hysum
  have hgcharsum := summable_character_mul_real χ hgsum
  have hDchar : (∑' n : ℕ, χ n * (D n : ℂ)) =
      characterPerronTentSum χ y - characterPerronTentSum χ x -
        (h : ℂ) * characterChebyshevPsi χ ⌊x⌋₊ := by
    calc
      _ = ∑' n : ℕ, ((χ n * (f y n : ℂ) - χ n * (f x n : ℂ)) - χ n * (g n : ℂ)) := by
        apply tsum_congr
        intro n
        dsimp only [D]
        push_cast
        ring
      _ = ((∑' n : ℕ, χ n * (f y n : ℂ)) - ∑' n : ℕ, χ n * (f x n : ℂ)) -
          ∑' n : ℕ, χ n * (g n : ℂ) := by
        rw [Summable.tsum_sub (hychar.sub hxchar) hgcharsum, Summable.tsum_sub hychar hxchar]
      _ = _ := by rw [hgchar]; rfl
  have hDscalar : (∑' n : ℕ, D n) = perronTentSum y - perronTentSum x - h * chebyshevPsi ⌊x⌋₊ := by
    rw [show D = fun n => (f y n - f x n) - g n from rfl,
      Summable.tsum_sub (hysum.sub hxsum) hgsum, Summable.tsum_sub hysum hxsum, hgscalar]
    rfl
  have hnorms := summable_norm_iff.mpr (summable_character_mul_real χ hDsum)
  change ‖characterPerronTentSum χ y - characterPerronTentSum χ x -
    (h : ℂ) * characterChebyshevPsi χ ⌊x⌋₊‖ ≤ _
  rw [← hDchar]
  calc
    _ ≤ ∑' n : ℕ, ‖χ n * (D n : ℂ)‖ := norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' n : ℕ, D n := hnorms.tsum_le_tsum (fun n => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hDpos n)]
      exact mul_le_of_le_one_left (hDpos n) (χ.norm_le_one _)) hDsum
    _ = perronTentSum y - perronTentSum x - h * chebyshevPsi ⌊x⌋₊ := hDscalar
    _ ≤ _ := by
      have hu := perronTent_sub_le_log_mul_psi hx hxy
      change perronTentSum y - perronTentSum x ≤ h * chebyshevPsi ⌊y⌋₊ at hu
      change _ ≤ h * (chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊)
      linarith only [hu]

/-- Quantitative cancellation in the actual unsmoothed character von Mangoldt sum.
Both the character tent rate and ordinary short-interval mass bound are proved inputs,
not assumptions on the character. -/
theorem exists_characterChebyshevPsi_power_log
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ rho C x₀ : ℝ, 0 < rho ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ‖characterChebyshevPsi χ ⌊x⌋₊‖ ≤
        C * x * Real.exp (-(rho * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨κ, C, X, hκ, hC, hX3, htent⟩ := exists_smoothed_character_vonMangoldt_power_log hχ
  obtain ⟨κψ, Cψ, Xψ, hκψ, hCψ, hXψ3, hpsi⟩ := exists_chebyshevPsi_power_log
  let rho := min (κ / 2) κψ
  have hrho : 0 < rho := lt_min (by positivity) hκψ
  have hrhoκ : rho ≤ κ / 2 := min_le_left _ _
  have hrhoψ : rho ≤ κψ := min_le_right _ _
  refine ⟨rho, 6 * C + 1 + 3 * Cψ, max X Xψ, hrho, by positivity,
    hX3.trans (le_max_left _ _), fun x hx => ?_⟩
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hxXψ : Xψ ≤ x := (le_max_right _ _).trans hx
  have hx3 : 3 ≤ x := hX3.trans hxX
  have hx0 : 0 < x := by linarith only [hx3]
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith only [hx3])
  let u := Real.log x ^ ((1 : ℝ) / 10)
  let ε := Real.exp (-(rho * u))
  let y := (1 + ε) * x
  let h := Real.log (1 + ε)
  have hu : 0 < u := Real.rpow_pos_of_pos hlogx _
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hrho.le hu.le))
  have hxy : x ≤ y := by dsimp only [y]; nlinarith only [hε, hx0]
  have hy0 : 0 < y := hx0.trans_le hxy
  have hy2 : y ≤ 2 * x := by dsimp only [y]; nlinarith only [hε1, hx0]
  have hlogy : u ≤ Real.log y ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow hlogx.le (Real.log_le_log hx0 hxy) (by positivity)
  have hhyx : Real.log (y / x) = h := by
    dsimp only [y, h]
    congr 1
    field_simp
  have hhε : ε / 2 ≤ h := by
    calc
      ε / 2 = 2 * ε / 4 := by ring
      _ ≤ 2 * ε / (ε + 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hε1])
      _ ≤ h := Real.le_log_one_add_of_nonneg hε.le
  have hh : 0 < h := (div_pos hε (by norm_num)).trans_le hhε
  have hdecay (b : ℝ) (hb : 0 ≤ b) :
      Real.exp (-(b * Real.log y ^ ((1 : ℝ) / 10))) ≤ Real.exp (-(b * u)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hlogy hb))
  have ht (z : ℝ) (hz : X ≤ z) : ‖characterPerronTentSum χ z‖ ≤
      C * z * Real.exp (-(κ * Real.log z ^ ((1 : ℝ) / 10))) := by
    simpa only [characterPerronTentSum, Complex.ofReal_mul, mul_assoc] using htent z hz
  have htx : ‖characterPerronTentSum χ x‖ ≤ C * x * Real.exp (-(κ * u)) := ht x hxX
  have hty : ‖characterPerronTentSum χ y‖ ≤ 2 * C * x * Real.exp (-(κ * u)) := by
    apply (ht y (hxX.trans hxy)).trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hy2 hC) (hdecay κ hκ.le)
      (Real.exp_nonneg _) (by positivity)).trans_eq (by ring)
  have hdef := norm_characterPerron_unsmoothing_defect χ hx0 hxy
  rw [hhyx] at hdef
  let P := characterChebyshevPsi χ ⌊x⌋₊
  let S := characterPerronTentSum χ y - characterPerronTentSum χ x
  have htriangle : h * ‖P‖ ≤ ‖characterPerronTentSum χ y‖ + ‖characterPerronTentSum χ x‖ +
      ‖S - (h : ℂ) * P‖ := by
    calc
      h * ‖P‖ = ‖(h : ℂ) * P‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      _ = ‖S - (S - (h : ℂ) * P)‖ := by congr 1; ring
      _ ≤ ‖S‖ + ‖S - (h : ℂ) * P‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add
        (norm_sub_le (characterPerronTentSum χ y) (characterPerronTentSum χ x)) le_rfl
  have hw : h * ‖P‖ ≤ 3 * C * x * Real.exp (-(κ * u)) +
      h * (chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊) := by
    change ‖S - (h : ℂ) * P‖ ≤ h * (chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊) at hdef
    linarith only [htriangle, htx, hty, hdef]
  have hrecover : ‖P‖ ≤ (3 * C * x * Real.exp (-(κ * u))) / h +
      (chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊) := by
    calc
      ‖P‖ = (h * ‖P‖) / h := by field_simp
      _ ≤ (3 * C * x * Real.exp (-(κ * u)) + h *
          (chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊)) / h := div_le_div_of_nonneg_right hw hh.le
      _ = _ := by field_simp
  have hfast : Real.exp (-(κ * u)) ≤ ε ^ (2 : ℕ) := by
    dsimp only [ε]
    rw [pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hκrho : 2 * rho ≤ κ := by linarith only [hrhoκ]
    have hm := mul_le_mul_of_nonneg_right hκrho hu.le
    linarith only [hm]
  have hrate : (3 * C * x * Real.exp (-(κ * u))) / h ≤ 6 * C * x * ε := by
    calc
      _ ≤ (3 * C * x * ε ^ (2 : ℕ)) / h :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfast (by positivity)) hh.le
      _ ≤ (3 * C * x * ε ^ (2 : ℕ)) / (ε / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hhε
      _ = _ := by field_simp; ring
  have hslow : Real.exp (-(κψ * u)) ≤ ε :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hrhoψ hu.le))
  have hpx : |chebyshevPsi ⌊x⌋₊ - x| ≤ Cψ * x * ε :=
    (hpsi x hxXψ).trans (mul_le_mul_of_nonneg_left hslow (by positivity))
  have hpy : |chebyshevPsi ⌊y⌋₊ - y| ≤ 2 * Cψ * x * ε := by
    apply (hpsi y (hxXψ.trans hxy)).trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hy2 hCψ) ((hdecay κψ hκψ.le).trans hslow)
      (Real.exp_nonneg _) (by positivity)).trans_eq (by ring)
  have hshort : chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊ ≤ (1 + 3 * Cψ) * x * ε := by
    have hupper := (abs_le.mp hpy).2
    have hlower := (abs_le.mp hpx).1
    have hgap : y - x = x * ε := by dsimp only [y]; ring
    linarith only [hupper, hlower, hgap]
  change ‖P‖ ≤ (6 * C + 1 + 3 * Cψ) * x * ε
  linarith only [hrecover, hrate, hshort]

end RHTower
