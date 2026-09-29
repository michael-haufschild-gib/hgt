import GaloisForLFunctions.RHTower.Matveev.HermiteApproximateSchwarz

/-!
# Hermite correction at the integer nodes `0, 1, …, X − 1`

For the nodes `{0, …, X − 1}` with multiplicity `M`:

* at an integer `x' < Y` with `X ≤ Y`, `|Ω(x')| ≤ Y^{MX}`;
* on the circle `|w| = ρ ≥ X`, `|Ω(w)| ≥ (ρ − X)^{MX}`;
* the node distances multiply to factorials, `∏_{y < X, y ≠ x} |x − y| = x! (X − 1 − x)!`, hence
  for `|z| ≤ ρ` the normalized node polynomial satisfies `|u_x(z)| ≤ (2^X e^{ρ + X})^M`;
* consequently, if every jet `f^{(t)}(x)`, `t < M`, is at most `ε`, then for `|z| ≤ ρ`
  `|H(z)| ≤ X · 2ε e^{ρ + X} · 2^M (2^X e^{ρ+X})^{M²}`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Metric

/-- The integer nodes `{0, …, X − 1} ⊂ ℂ`. -/
def natNodes (X : ℕ) : Finset ℂ := (range X).image (fun y : ℕ => (y : ℂ))

theorem card_natNodes (X : ℕ) : #(natNodes X) = X := by
  rw [natNodes, card_image_of_injective _ Nat.cast_injective, card_range]

theorem hermiteNodePoly_natNodes (X M : ℕ) (z : ℂ) :
    hermiteNodePoly (natNodes X) M z = ∏ y ∈ range X, (z - y) ^ M := by
  rw [hermiteNodePoly, natNodes, prod_image fun a _ b _ h => Nat.cast_injective h]

theorem natNodes_erase (X x : ℕ) :
    (natNodes X).erase (x : ℂ) = ((range X).erase x).image (fun y : ℕ => (y : ℂ)) := by
  rw [natNodes, image_erase Nat.cast_injective]

/-- At an integer point below `Y` the node polynomial is at most `Y^{MX}`. -/
theorem norm_hermiteNodePoly_natNodes_le {X Y : ℕ} (hXY : X ≤ Y) (M : ℕ) {x' : ℕ}
    (hx' : x' < Y) : ‖hermiteNodePoly (natNodes X) M (x' : ℂ)‖ ≤ (Y : ℝ) ^ (M * X) := by
  rw [hermiteNodePoly_natNodes, norm_prod]
  calc ∏ y ∈ range X, ‖((x' : ℂ) - y) ^ M‖ ≤ ∏ _y ∈ range X, (Y : ℝ) ^ M := by
        refine prod_le_prod (fun _ _ => norm_nonneg _) fun y hy => ?_
        rw [norm_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ M
        have hy' : (y : ℝ) < Y := by exact_mod_cast (mem_range.mp hy).trans_le hXY
        have h1 : (x' : ℝ) < Y := by exact_mod_cast hx'
        have h3 : (0 : ℝ) ≤ x' := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
        rw [show ((x' : ℂ) - y) = (((x' : ℝ) - y : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith
    _ = (Y : ℝ) ^ (M * X) := by rw [prod_const, card_range, ← pow_mul]

/-- On the circle `|w| = ρ ≥ X` the node polynomial is at least `(ρ − X)^{MX}`. -/
theorem le_norm_hermiteNodePoly_natNodes {X : ℕ} (M : ℕ) {ρ : ℝ} (hXρ : (X : ℝ) ≤ ρ) {w : ℂ}
    (hw : ‖w‖ = ρ) : (ρ - X) ^ (M * X) ≤ ‖hermiteNodePoly (natNodes X) M w‖ := by
  have h0 : 0 ≤ ρ - X := sub_nonneg.mpr hXρ
  rw [hermiteNodePoly_natNodes, norm_prod]
  calc (ρ - X) ^ (M * X) = ∏ _y ∈ range X, (ρ - X) ^ M := by
        rw [prod_const, card_range, ← pow_mul]
    _ ≤ ∏ y ∈ range X, ‖(w - y) ^ M‖ := by
        refine prod_le_prod (fun _ _ => pow_nonneg h0 _) fun y hy => ?_
        rw [norm_pow]
        refine pow_le_pow_left₀ h0 ?_ M
        have hy' : (y : ℝ) ≤ X := by exact_mod_cast (mem_range.mp hy).le
        have := norm_sub_norm_le w (y : ℂ)
        rw [hw, Complex.norm_natCast] at this
        linarith

/-- **Node distances multiply to factorials.** -/
theorem prod_abs_natCast_sub (x j : ℕ) :
    ∏ y ∈ (range (x + 1 + j)).erase x, |(x : ℝ) - y| = (x.factorial : ℝ) * j.factorial := by
  induction j with
  | zero =>
      rw [add_zero, range_add_one, erase_insert notMem_range_self, Nat.factorial_zero,
        Nat.cast_one, mul_one, ← prod_range_reflect]
      have hterm : ∀ y ∈ range x, |(x : ℝ) - ((x - 1 - y : ℕ) : ℝ)| = ((y + 1 : ℕ) : ℝ) := by
        intro y hy
        have hy' := mem_range.mp hy
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        rw [abs_of_nonneg (by linarith)]
        ring
      rw [prod_congr rfl hterm, ← Nat.cast_prod, prod_range_add_one_eq_factorial]
  | succ j ih =>
      rw [show x + 1 + (j + 1) = x + 1 + j + 1 by ring, range_add_one,
        erase_insert_of_ne (by omega), prod_insert (by simp), ih, Nat.factorial_succ]
      push_cast
      rw [show (x : ℝ) - (x + 1 + j) = -(j + 1) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
      ring

/-- **The normalized node polynomial is at most `(2^X e^{ρ+X})^M` on `|z| ≤ ρ`.** -/
theorem norm_hermiteRatio_natNodes_le {X : ℕ} (M : ℕ) {x : ℕ} (hx : x < X) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {z : ℂ} (hz : ‖z‖ ≤ ρ) :
    ‖hermiteRatio (natNodes X) M (x : ℂ) z‖ ≤ (2 ^ X * Real.exp (ρ + X)) ^ M := by
  obtain ⟨j, rfl⟩ : ∃ j, X = x + 1 + j := ⟨X - x - 1, by omega⟩
  have hinj : ∀ a ∈ (range (x + 1 + j)).erase x, ∀ b ∈ (range (x + 1 + j)).erase x,
      (a : ℂ) = b → a = b := fun a _ b _ h => Nat.cast_injective h
  rw [hermiteRatio, hermiteNodePoly, hermiteNodePoly, natNodes_erase, prod_image hinj,
    prod_image hinj, norm_div, norm_prod, norm_prod]
  simp only [norm_pow]
  rw [prod_pow, prod_pow, ← div_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ M
  have hQ : ∏ y ∈ (range (x + 1 + j)).erase x, ‖(x : ℂ) - y‖ =
      (x.factorial : ℝ) * j.factorial := by
    rw [← prod_abs_natCast_sub]
    refine prod_congr rfl fun y _ => ?_
    rw [show ((x : ℂ) - y) = (((x : ℝ) - y : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
  have hXr : (0 : ℝ) ≤ ρ + ((x + 1 + j : ℕ) : ℝ) := by positivity
  have hP : ∏ y ∈ (range (x + 1 + j)).erase x, ‖z - y‖ ≤
      (ρ + ((x + 1 + j : ℕ) : ℝ)) ^ (x + j) := by
    calc ∏ y ∈ (range (x + 1 + j)).erase x, ‖z - y‖
        ≤ ∏ _y ∈ (range (x + 1 + j)).erase x, (ρ + ((x + 1 + j : ℕ) : ℝ)) := by
          refine prod_le_prod (fun _ _ => norm_nonneg _) fun y hy => ?_
          have hy' : (y : ℝ) ≤ ((x + 1 + j : ℕ) : ℝ) := by
            exact_mod_cast (mem_range.mp (mem_of_mem_erase hy)).le
          calc ‖z - y‖ ≤ ‖z‖ + ‖(y : ℂ)‖ := norm_sub_le _ _
            _ ≤ ρ + ((x + 1 + j : ℕ) : ℝ) := by rw [Complex.norm_natCast]; linarith
      _ = (ρ + ((x + 1 + j : ℕ) : ℝ)) ^ (x + j) := by
          rw [prod_const, card_erase_of_mem (mem_range.mpr (by omega)), card_range]
          congr 1
          omega
  have hfact : ((x + j).factorial : ℝ) ≤ 2 ^ (x + j) * (x.factorial * j.factorial) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show x ≤ x + j by omega)
    rw [Nat.add_sub_cancel_left] at h
    have : (x + j).factorial ≤ 2 ^ (x + j) * (x.factorial * j.factorial) := by
      rw [← h, mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    exact_mod_cast this
  have hexp := Real.pow_div_factorial_le_exp _ hXr (x + j)
  rw [div_le_iff₀ (by positivity)] at hexp
  have h2 : (2 : ℝ) ^ (x + j) ≤ 2 ^ (x + 1 + j) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [hQ, div_le_iff₀ (by positivity)]
  calc ∏ y ∈ (range (x + 1 + j)).erase x, ‖z - y‖
      ≤ (ρ + ((x + 1 + j : ℕ) : ℝ)) ^ (x + j) := hP
    _ ≤ Real.exp (ρ + ((x + 1 + j : ℕ) : ℝ)) * ((x + j).factorial : ℝ) := hexp
    _ ≤ Real.exp (ρ + ((x + 1 + j : ℕ) : ℝ)) * (2 ^ (x + j) * (x.factorial * j.factorial)) := by
        gcongr
    _ ≤ Real.exp (ρ + ((x + 1 + j : ℕ) : ℝ)) * (2 ^ (x + 1 + j) * (x.factorial * j.factorial)) := by
        gcongr
    _ = 2 ^ (x + 1 + j) * Real.exp (ρ + ((x + 1 + j : ℕ) : ℝ)) *
          ((x.factorial : ℝ) * j.factorial) := by ring

/-- The bound for the Hermite correction at the integer nodes. -/
def integerHermiteBound (X M : ℕ) (ρ ε : ℝ) : ℝ :=
  X * (2 * ε * Real.exp (ρ + X) * (2 ^ M * (2 ^ X * Real.exp (ρ + X)) ^ (M * M)))

theorem integerHermiteBound_nonneg (X M : ℕ) {ρ ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ integerHermiteBound X M ρ ε := by
  unfold integerHermiteBound
  positivity

/-- **Size of the Hermite correction at the integer nodes.** -/
theorem norm_hermiteCorrection_natNodes_le {f : ℂ → ℂ} {X M : ℕ} {ε ρ : ℝ} (hε : 0 ≤ ε)
    (hρ : 0 ≤ ρ) (hsmall : ∀ x < X, ∀ t < M, ‖iteratedDeriv t f (x : ℂ)‖ ≤ ε) {z : ℂ}
    (hz : ‖z‖ ≤ ρ) : ‖hermiteCorrection f (natNodes X) M z‖ ≤ integerHermiteBound X M ρ ε := by
  refine (norm_hermiteCorrection_le hε (fun c hc t ht => ?_) z).trans ?_
  · obtain ⟨x, hx, rfl⟩ := mem_image.mp hc
    exact hsmall x (mem_range.mp hx) t ht
  · rw [natNodes, sum_image fun a _ b _ h => Nat.cast_injective h]
    have hV : (1 : ℝ) ≤ 2 ^ X * Real.exp (ρ + X) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
        (Real.one_le_exp (by positivity))
    calc ∑ x ∈ range X, 2 * ε * Real.exp ‖z - x‖ * (1 + ‖hermiteRatio (natNodes X) M x z‖) ^ M
        ≤ ∑ _x ∈ range X, 2 * ε * Real.exp (ρ + X) *
            (2 ^ M * (2 ^ X * Real.exp (ρ + X)) ^ (M * M)) := by
          refine sum_le_sum fun x hx => ?_
          have hx' := mem_range.mp hx
          have hdist : ‖z - x‖ ≤ ρ + X := by
            have h1 : (x : ℝ) ≤ X := by exact_mod_cast hx'.le
            calc ‖z - x‖ ≤ ‖z‖ + ‖(x : ℂ)‖ := norm_sub_le _ _
              _ ≤ ρ + X := by rw [Complex.norm_natCast]; linarith
          have hu := norm_hermiteRatio_natNodes_le M hx' hρ hz
          have hVM : (1 : ℝ) ≤ (2 ^ X * Real.exp (ρ + X)) ^ M := one_le_pow₀ hV
          have hone : (1 + ‖hermiteRatio (natNodes X) M x z‖) ^ M ≤
              2 ^ M * (2 ^ X * Real.exp (ρ + X)) ^ (M * M) := by
            calc (1 + ‖hermiteRatio (natNodes X) M x z‖) ^ M
                ≤ (2 * (2 ^ X * Real.exp (ρ + X)) ^ M) ^ M := by
                  gcongr
                  linarith
              _ = 2 ^ M * (2 ^ X * Real.exp (ρ + X)) ^ (M * M) := by
                  rw [mul_pow, ← pow_mul]
          gcongr
      _ = integerHermiteBound X M ρ ε := by
          rw [sum_const, card_range, nsmul_eq_mul, integerHermiteBound]

end GaloisForLFunctions.RHTower.Matveev
