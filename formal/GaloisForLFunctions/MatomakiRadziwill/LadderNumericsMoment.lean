import GaloisForLFunctions.MatomakiRadziwill.LadderNumerics

/-!
# The moment step, numerically

Scale `j−1` has primes in `[P', Q']` and width `H' ≥ 3`; scale `j` has primes in `[P, Q]`, `Q ≤ X`, and
width `H`.  For blocks `u` (scale `j−1`) and `v` (scale `j`) let `ℓ = ⌈(v/H)/(u/H')⌉`
(`momentExp`).  Then `ℓ u/H' ≥ v/H`, so the product `Q_u^ℓ R_v` has length at least `X ≥ W`, and
`ℓ u/H' < v/H + u/H'`, so the threshold ratio is at most `e^{2αu/H'} ≤ Q'^{2α}`
(`moment_pair_le`):

`e^{-2αv/H} e^{2αℓu/H'} ∫ |Q_u^ℓ R_v|² ≤ Q'^{2α} · 144 (18ℓ/H')^ℓ`.

When `18eℓ ≤ H'` the last factor is at most `144 e^{-ℓ} ≤ 144 e^{-(log P − 1/H)/log Q'}`
(`pow_le_exp_neg`, `moment_step_le`).
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The moment exponent `ℓ = ⌈(v/H)/(u/H')⌉`. -/
def momentExp (H H' : ℝ) (u v : ℕ) : ℕ := ⌈((v : ℝ) / H) / ((u : ℝ) / H')⌉₊

theorem momentExp_bounds {H H' : ℝ} (hH : 0 < H) (hH' : 0 < H') {u v : ℕ} (hu : 1 ≤ u)
    (hv : 1 ≤ v) :
    1 ≤ momentExp H H' u v ∧ (v : ℝ) / H ≤ momentExp H H' u v * ((u : ℝ) / H')
      ∧ (momentExp H H' u v : ℝ) * ((u : ℝ) / H') < (v : ℝ) / H + (u : ℝ) / H' := by
  have hu0 : (0 : ℝ) < (u : ℝ) / H' := by
    have : (1 : ℝ) ≤ u := by exact_mod_cast hu
    positivity
  have hv0 : (0 : ℝ) < (v : ℝ) / H := by
    have : (1 : ℝ) ≤ v := by exact_mod_cast hv
    positivity
  have hq0 : 0 < ((v : ℝ) / H) / ((u : ℝ) / H') := div_pos hv0 hu0
  have hle := Nat.le_ceil (((v : ℝ) / H) / ((u : ℝ) / H'))
  have hlt := Nat.ceil_lt_add_one hq0.le
  refine ⟨Nat.one_le_iff_ne_zero.mpr (by
    intro h; unfold momentExp at h; rw [Nat.ceil_eq_zero] at h; linarith), ?_, ?_⟩
  · unfold momentExp
    calc (v : ℝ) / H = ((v : ℝ) / H) / ((u : ℝ) / H') * ((u : ℝ) / H') := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hle hu0.le
  · unfold momentExp
    calc (⌈((v : ℝ) / H) / ((u : ℝ) / H')⌉₊ : ℝ) * ((u : ℝ) / H')
        < (((v : ℝ) / H) / ((u : ℝ) / H') + 1) * ((u : ℝ) / H') :=
          mul_lt_mul_of_pos_right hlt hu0
      _ = (v : ℝ) / H + (u : ℝ) / H' := by field_simp

/-- **One pair of blocks.** -/
theorem moment_pair_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {Pr' : Finset ℕ}
    (hPr' : ∀ q ∈ Pr', q.Prime) {H' : ℝ} (hH' : 3 ≤ H') {P' Q' : ℝ} (hP'1 : 1 ≤ P')
    (hPr'b : ∀ p ∈ Pr', P' ≤ p ∧ (p : ℝ) ≤ Q') (hP'H : Real.exp 1 * H' ≤ P')
    (hu2 : 2 ≤ H' * Real.log P') {Pr : Finset ℕ} (rest : ℕ → Prop) [DecidablePred rest]
    {X : ℕ} {H : ℝ} (hH : 0 < H) {P Q : ℝ} (hP1 : 1 ≤ P) (hPrb : ∀ p ∈ Pr, P ≤ p ∧ (p : ℝ) ≤ Q)
    (hQX : Q ≤ X) (hv2 : 2 ≤ H * Real.log P) {α : ℝ} (hα0 : 0 ≤ α) {W : ℝ} (hW : 1 ≤ W)
    (hWX : W ≤ X) {u v : ℕ} (hu : u ∈ Pr'.image (blk H')) (hv : v ∈ Pr.image (blk H)) :
    Real.exp (-α * v / H) ^ 2 / Real.exp (-α * u / H') ^ (2 * momentExp H H' u v)
        * (∫ w in Icc (-W) W, ‖blockQ f Pr' H' u w ^ momentExp H H' u v
            * blockR f Pr rest X H v w‖ ^ 2)
      ≤ Q' ^ (2 * α) * (144 * (18 * momentExp H H' u v / H') ^ momentExp H H' u v) := by
  have hH'0 : 0 < H' := by linarith
  obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hu1, hu2'⟩ := blk_bounds hH'0 hP'1 (hPr'b p' hp').1 (hPr'b p' hp').2
  obtain ⟨hv1, hv2'⟩ := blk_bounds hH hP1 (hPrb p hp).1 (hPrb p hp).2
  set u := blk H' p' with hudef
  set v := blk H p with hvdef
  have huge1 : 1 ≤ u := by
    have : (1 : ℝ) ≤ u := by linarith
    exact_mod_cast this
  have hvge1 : 1 ≤ v := by
    have : (1 : ℝ) ≤ v := by linarith
    exact_mod_cast this
  obtain ⟨hℓ1, hℓlow, hℓup⟩ := momentExp_bounds hH hH'0 huge1 hvge1
  set ℓ := momentExp H H' u v with hℓdef
  have hQ'1 : 1 ≤ Q' := le_trans hP'1 (le_trans (hPr'b p' hp').1 (hPr'b p' hp').2)
  have hQ1 : 1 ≤ Q := le_trans hP1 (le_trans (hPrb p hp).1 (hPrb p hp).2)
  -- the hypotheses of the moment computation
  have hS : H' ≤ Real.exp ((u : ℝ) / H') := by
    have h1 : Real.log P' - 1 ≤ (u : ℝ) / H' := by
      rw [le_div_iff₀ hH'0]
      have : 1 ≤ H' := by linarith
      nlinarith
    calc H' ≤ P' / Real.exp 1 := by rw [le_div_iff₀ (Real.exp_pos 1)]; linarith
      _ = Real.exp (Real.log P' - 1) := by
          rw [Real.exp_sub, Real.exp_log (by linarith)]
      _ ≤ Real.exp ((u : ℝ) / H') := Real.exp_le_exp.mpr h1
  have hvlog : (v : ℝ) / H ≤ Real.log X := by
    rw [div_le_iff₀ hH]
    have : Real.log Q ≤ Real.log X := Real.log_le_log (by linarith) hQX
    nlinarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hlo_eq : cofLo X H v = X * Real.exp (-((v : ℝ) / H)) := by
    rw [cofLo]; congr 2; ring
  have hlo : 1 ≤ cofLo X H v := by
    rw [hlo_eq, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    calc Real.exp ((v : ℝ) / H) ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr hvlog
      _ = X := Real.exp_log hX0
  have hlen : W ≤ Real.exp ((u : ℝ) / H') ^ ℓ * cofLo X H v := by
    rw [← Real.exp_nat_mul, hlo_eq]
    have h1 : Real.exp ((v : ℝ) / H) ≤ Real.exp (ℓ * ((u : ℝ) / H')) :=
      Real.exp_le_exp.mpr hℓlow
    have h2 : Real.exp (ℓ * ((u : ℝ) / H')) * (X * Real.exp (-((v : ℝ) / H)))
        ≥ Real.exp ((v : ℝ) / H) * (X * Real.exp (-((v : ℝ) / H))) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : Real.exp ((v : ℝ) / H) * (X * Real.exp (-((v : ℝ) / H))) = X := by
      rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    linarith
  have hmom := integral_normSq_blockQ_pow_mul_blockR_le hf hPr' hH' u ℓ hℓ1 hS Pr rest X H v hlo
    hW hlen
  -- the threshold ratio
  have hratio : Real.exp (-α * v / H) ^ 2 / Real.exp (-α * u / H') ^ (2 * ℓ) ≤ Q' ^ (2 * α) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub, Real.rpow_def_of_pos (by linarith)]
    refine Real.exp_le_exp.mpr ?_
    have hulog : (u : ℝ) / H' ≤ Real.log Q' := by rw [div_le_iff₀ hH'0]; linarith
    push_cast
    have e1 : (2 : ℝ) * (-α * v / H) - 2 * ℓ * (-α * u / H')
        = 2 * α * (ℓ * ((u : ℝ) / H') - (v : ℝ) / H) := by ring
    rw [e1]
    have h1 : ℓ * ((u : ℝ) / H') - (v : ℝ) / H ≤ Real.log Q' := by linarith
    nlinarith
  have hint0 : 0 ≤ ∫ w in Icc (-W) W, ‖blockQ f Pr' H' u w ^ ℓ * blockR f Pr rest X H v w‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun w _ => by positivity
  have hratio0 : 0 ≤ Real.exp (-α * v / H) ^ 2 / Real.exp (-α * u / H') ^ (2 * ℓ) := by positivity
  calc Real.exp (-α * v / H) ^ 2 / Real.exp (-α * u / H') ^ (2 * ℓ)
        * (∫ w in Icc (-W) W, ‖blockQ f Pr' H' u w ^ ℓ * blockR f Pr rest X H v w‖ ^ 2)
      ≤ Q' ^ (2 * α) * (144 * (18 * ℓ / H') ^ ℓ) :=
        mul_le_mul hratio hmom hint0 (Real.rpow_nonneg (by linarith) _)

/-- `x^ℓ ≤ e^{-ℓ}` for `0 ≤ x ≤ 1/e`. -/
theorem pow_le_exp_neg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.exp (-1)) (ℓ : ℕ) :
    x ^ ℓ ≤ Real.exp (-(ℓ : ℝ)) := by
  calc x ^ ℓ ≤ Real.exp (-1) ^ ℓ := pow_le_pow_left₀ hx0 hx ℓ
    _ = Real.exp (-(ℓ : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- **A whole moment step.**  If `18e(log Q/(log P' − 1/H') + 1) ≤ H'`, every exponent satisfies
`18eℓ ≤ H'`, and the step is at most `#V² #V' Q'^{2α} · 144 e^{-(log P − 1/H)/log Q'}`. -/
theorem moment_step_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {Pr' : Finset ℕ}
    (hPr' : ∀ q ∈ Pr', q.Prime) {H' : ℝ} (hH' : 3 ≤ H') {P' Q' : ℝ} (hP'1 : 1 ≤ P')
    (hPr'b : ∀ p ∈ Pr', P' ≤ p ∧ (p : ℝ) ≤ Q') (hP'H : Real.exp 1 * H' ≤ P')
    (hu2 : 2 ≤ H' * Real.log P') {Pr : Finset ℕ} (rest : ℕ → Prop) [DecidablePred rest]
    {X : ℕ} {H : ℝ} (hH : 0 < H) {P Q : ℝ} (hP1 : 1 ≤ P) (hPrb : ∀ p ∈ Pr, P ≤ p ∧ (p : ℝ) ≤ Q)
    (hQX : Q ≤ X) (hv2 : 2 ≤ H * Real.log P) {α : ℝ} (hα0 : 0 ≤ α) {W : ℝ} (hW : 1 ≤ W)
    (hWX : W ≤ X) (hQ'1 : 1 ≤ Q')
    (hup : 18 * Real.exp 1 * (Real.log Q / (Real.log P' - 1 / H') + 1) ≤ H') :
    ((Pr.image (blk H)).card : ℝ) * ∑ v ∈ Pr.image (blk H), ∑ u ∈ Pr'.image (blk H'),
        Real.exp (-α * v / H) ^ 2 / Real.exp (-α * u / H') ^ (2 * momentExp H H' u v)
        * (∫ w in Icc (-W) W, ‖blockQ f Pr' H' u w ^ momentExp H H' u v
            * blockR f Pr rest X H v w‖ ^ 2)
      ≤ ((Pr.image (blk H)).card : ℝ) ^ 2 * (Pr'.image (blk H')).card * Q' ^ (2 * α)
          * (144 * Real.exp (-((Real.log P - 1 / H) / Real.log Q'))) := by
  classical
  have hH'0 : 0 < H' := by linarith
  set V := Pr.image (blk H) with hV
  set V' := Pr'.image (blk H') with hV'
  set B : ℝ := Q' ^ (2 * α) * (144 * Real.exp (-((Real.log P - 1 / H) / Real.log Q'))) with hB
  have hpair : ∀ v ∈ V, ∀ u ∈ V', Real.exp (-α * v / H) ^ 2
      / Real.exp (-α * u / H') ^ (2 * momentExp H H' u v)
      * (∫ w in Icc (-W) W, ‖blockQ f Pr' H' u w ^ momentExp H H' u v
          * blockR f Pr rest X H v w‖ ^ 2) ≤ B := by
    intro v hv u hu
    refine le_trans (moment_pair_le hf hPr' hH' hP'1 hPr'b hP'H hu2 rest hH hP1 hPrb hQX hv2
      hα0 hW hWX hu hv) ?_
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hu1, hu2'⟩ := blk_bounds hH'0 hP'1 (hPr'b p' hp').1 (hPr'b p' hp').2
    obtain ⟨hv1, hv2'⟩ := blk_bounds hH hP1 (hPrb p hp).1 (hPrb p hp).2
    have huge1 : 1 ≤ blk H' p' := by
      have : (1 : ℝ) ≤ blk H' p' := by linarith
      exact_mod_cast this
    have hvge1 : 1 ≤ blk H p := by
      have : (1 : ℝ) ≤ blk H p := by linarith
      exact_mod_cast this
    obtain ⟨-, hℓlow, hℓup⟩ := momentExp_bounds hH hH'0 huge1 hvge1
    set ℓ := momentExp H H' (blk H' p') (blk H p) with hℓdef
    set a : ℝ := (blk H' p' : ℝ) / H' with ha
    set b : ℝ := (blk H p : ℝ) / H with hb
    have ha_low : Real.log P' - 1 / H' ≤ a := by
      rw [ha, le_div_iff₀ hH'0]; field_simp; linarith
    have ha_up : a ≤ Real.log Q' := by rw [ha, div_le_iff₀ hH'0]; linarith
    have hb_up : b ≤ Real.log (Q) := by rw [hb, div_le_iff₀ hH]; linarith
    have hb_low : Real.log P - 1 / H ≤ b := by
      rw [hb, le_div_iff₀ hH]; field_simp; linarith
    have hlogP' : 1 / H' < Real.log P' := by
      have : 2 / H' ≤ Real.log P' := by rw [div_le_iff₀ hH'0]; linarith
      have : 1 / H' < 2 / H' := by rw [div_lt_div_iff_of_pos_right hH'0]; norm_num
      linarith
    have ha0 : 0 < a := by linarith
    -- `ℓ ≤ log Q/(log P' − 1/H') + 1`
    have hℓmax : (ℓ : ℝ) ≤ Real.log Q / (Real.log P' - 1 / H') + 1 := by
      have h1 : (ℓ : ℝ) < b / a + 1 := by
        have h2 : (ℓ : ℝ) * a < b + a := hℓup
        rw [div_add_one ha0.ne', lt_div_iff₀ ha0]
        linarith
      have h3 : b / a ≤ Real.log Q / (Real.log P' - 1 / H') := by
        have hb0 : 0 ≤ b := by rw [hb]; positivity
        calc b / a ≤ Real.log Q / a := div_le_div_of_nonneg_right hb_up ha0.le
          _ ≤ Real.log Q / (Real.log P' - 1 / H') :=
              div_le_div_of_nonneg_left (le_trans hb0 hb_up) (by linarith) ha_low
      linarith
    -- `ℓ ≥ (log P − 1/H)/log Q'`
    have hlogQ'0 : 0 < Real.log Q' := lt_of_lt_of_le (by linarith) ha_up
    have hℓmin : (Real.log P - 1 / H) / Real.log Q' ≤ ℓ := by
      have h1 : b ≤ ℓ * a := hℓlow
      rw [div_le_iff₀ hlogQ'0]
      have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
      nlinarith
    -- the geometric factor
    have h18 : 18 * Real.exp 1 * ℓ ≤ H' := by
      have h1 : 18 * Real.exp 1 * ℓ ≤ 18 * Real.exp 1
          * (Real.log Q / (Real.log P' - 1 / H') + 1) :=
        mul_le_mul_of_nonneg_left hℓmax (by positivity)
      linarith
    have hx : 18 * (ℓ : ℝ) / H' ≤ Real.exp (-1) := by
      rw [Real.exp_neg, div_le_iff₀ hH'0, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos 1)]
      linarith
    have hgeo : (18 * (ℓ : ℝ) / H') ^ ℓ ≤ Real.exp (-((Real.log P - 1 / H) / Real.log Q')) := by
      refine le_trans (pow_le_exp_neg (by positivity) hx ℓ) (Real.exp_le_exp.mpr ?_)
      linarith
    rw [hB]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) _)
    linarith
  have hB0 : 0 ≤ B := by
    rw [hB]
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ Q' by linarith) (2 * α)
    positivity
  calc (V.card : ℝ) * ∑ v ∈ V, ∑ u ∈ V', Real.exp (-α * v / H) ^ 2
        / Real.exp (-α * u / H') ^ (2 * momentExp H H' u v)
        * (∫ w in Icc (-W) W, ‖blockQ f Pr' H' u w ^ momentExp H H' u v
            * blockR f Pr rest X H v w‖ ^ 2)
      ≤ (V.card : ℝ) * ∑ _v ∈ V, ∑ _u ∈ V', B := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun v hv => sum_le_sum fun u hu =>
          hpair v hv u hu) (Nat.cast_nonneg _)
    _ = (V.card : ℝ) ^ 2 * V'.card * B := by
        rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
    _ = (V.card : ℝ) ^ 2 * V'.card * Q' ^ (2 * α)
          * (144 * Real.exp (-((Real.log P - 1 / H) / Real.log Q'))) := by
        rw [hB]; ring

end

end GaloisForLFunctions.MatomakiRadziwill
