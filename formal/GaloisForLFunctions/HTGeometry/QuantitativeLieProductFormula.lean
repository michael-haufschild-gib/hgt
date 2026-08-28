import GaloisForLFunctions.HTGeometry.KrylovProjectedCompleteIncidenceLaw

open Set NormedSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [CStarAlgebra A]

theorem cstarExponentialTaylor_one (x : A) (t : ℝ) :
    cstarExponentialTaylor x 1 t = 1 + t • x := by
  rw [show cstarExponentialTaylor x 1 t =
      (∑ k ∈ Finset.range 2, (t ^ k / (k.factorial : ℝ)) • x ^ k) by
        simp [cstarExponentialTaylor]]
  norm_num [Finset.sum_range_succ]

variable [Nontrivial A]

theorem norm_exp_mul_exp_sub_exp_add_le
    (x y : A) (hx : x ∈ skewAdjoint A) (hy : y ∈ skewAdjoint A)
    (t : ℝ) (hsmall : |t| * (‖x‖ + ‖y‖) ≤ 1) :
    ‖exp (t • x) * exp (t • y) - exp (t • (x + y))‖ ≤
      3 * (‖x‖ + ‖y‖) ^ 2 * |t| ^ 2 := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let Tx : A := 1 + t • x
  let Ty : A := 1 + t • y
  let Txy : A := 1 + t • (x + y)
  have hxy : x + y ∈ skewAdjoint A := (skewAdjoint A).add_mem hx hy
  have hRx : ‖exp (t • x) - Tx‖ ≤ ‖x‖ ^ 2 * |t| ^ 2 / 2 := by
    simpa [Tx, cstarExponentialTaylor_one] using
      norm_exp_sub_cstarExponentialTaylor_le x hx 1 t
  have hRy : ‖exp (t • y) - Ty‖ ≤ ‖y‖ ^ 2 * |t| ^ 2 / 2 := by
    simpa [Ty, cstarExponentialTaylor_one] using
      norm_exp_sub_cstarExponentialTaylor_le y hy 1 t
  have hRxy : ‖exp (t • (x + y)) - Txy‖ ≤
      ‖x + y‖ ^ 2 * |t| ^ 2 / 2 := by
    simpa [Txy, cstarExponentialTaylor_one] using
      norm_exp_sub_cstarExponentialTaylor_le (x + y) hxy 1 t
  have hexpy : ‖exp (t • y)‖ = 1 := by
    exact CStarRing.norm_of_mem_unitary
      (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hy))
  have hTx : ‖Tx‖ ≤ 2 := by
    calc
      ‖Tx‖ ≤ ‖(1 : A)‖ + ‖t • x‖ := by
        simpa [Tx] using norm_add_le (1 : A) (t • x)
      _ = 1 + |t| * ‖x‖ := by simp [norm_smul, Real.norm_eq_abs]
      _ ≤ 2 := by
        have hxnonneg : 0 ≤ |t| * ‖y‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
        nlinarith
  have hcross : ‖Tx * Ty - Txy‖ ≤
      (‖x‖ + ‖y‖) ^ 2 * |t| ^ 2 := by
    have hid : Tx * Ty - Txy = t ^ 2 • (x * y) := by
      dsimp [Tx, Ty, Txy]
      simp only [add_mul, mul_add, one_mul, mul_one]
      rw [smul_mul_smul]
      module
    rw [hid, norm_smul, Real.norm_eq_abs]
    have ht_sq : |t ^ 2| = |t| ^ 2 := by rw [abs_pow]
    rw [ht_sq]
    calc
      |t| ^ 2 * ‖x * y‖ ≤ |t| ^ 2 * (‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (sq_nonneg _)
      _ ≤ (‖x‖ + ‖y‖) ^ 2 * |t| ^ 2 := by
        have hx0 := norm_nonneg x
        have hy0 := norm_nonneg y
        nlinarith [mul_nonneg hx0 hy0]
  have hsplit :
      exp (t • x) * exp (t • y) - exp (t • (x + y)) =
        (exp (t • x) - Tx) * exp (t • y) +
        Tx * (exp (t • y) - Ty) +
        (Tx * Ty - Txy) +
        (Txy - exp (t • (x + y))) := by
    noncomm_ring
  rw [hsplit]
  calc
    ‖(exp (t • x) - Tx) * exp (t • y) +
        Tx * (exp (t • y) - Ty) +
        (Tx * Ty - Txy) +
        (Txy - exp (t • (x + y)))‖
        ≤ ‖(exp (t • x) - Tx) * exp (t • y)‖ +
          ‖Tx * (exp (t • y) - Ty)‖ +
          ‖Tx * Ty - Txy‖ +
          ‖Txy - exp (t • (x + y))‖ := by
            calc
              _ ≤ ‖(exp (t • x) - Tx) * exp (t • y) +
                    Tx * (exp (t • y) - Ty) + (Tx * Ty - Txy)‖ +
                    ‖Txy - exp (t • (x + y))‖ := norm_add_le _ _
              _ ≤ (‖(exp (t • x) - Tx) * exp (t • y) +
                    Tx * (exp (t • y) - Ty)‖ + ‖Tx * Ty - Txy‖) +
                    ‖Txy - exp (t • (x + y))‖ := by gcongr; exact norm_add_le _ _
              _ ≤ ((‖(exp (t • x) - Tx) * exp (t • y)‖ +
                    ‖Tx * (exp (t • y) - Ty)‖) + ‖Tx * Ty - Txy‖) +
                    ‖Txy - exp (t • (x + y))‖ := by gcongr; exact norm_add_le _ _
              _ = _ := by ring
    _ ≤ (‖x‖ ^ 2 * |t| ^ 2 / 2) +
          2 * (‖y‖ ^ 2 * |t| ^ 2 / 2) +
          (‖x‖ + ‖y‖) ^ 2 * |t| ^ 2 +
          (‖x + y‖ ^ 2 * |t| ^ 2 / 2) := by
      have hterm1 : ‖(exp (t • x) - Tx) * exp (t • y)‖ ≤
          ‖x‖ ^ 2 * |t| ^ 2 / 2 := by
        rw [CStarRing.norm_mul_mem_unitary _
          (exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hy))]
        exact hRx
      have hterm2 : ‖Tx * (exp (t • y) - Ty)‖ ≤
          2 * (‖y‖ ^ 2 * |t| ^ 2 / 2) := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul hTx hRy (norm_nonneg _) (by positivity))
      have hterm4 : ‖Txy - exp (t • (x + y))‖ ≤
          ‖x + y‖ ^ 2 * |t| ^ 2 / 2 := by
        rw [norm_sub_rev]
        exact hRxy
      linarith
    _ ≤ 3 * (‖x‖ + ‖y‖) ^ 2 * |t| ^ 2 := by
      have hx0 := norm_nonneg x
      have hy0 := norm_nonneg y
      have ht0 := sq_nonneg |t|
      have hxy_norm := norm_add_le x y
      have hxB : ‖x‖ ≤ ‖x‖ + ‖y‖ := by linarith
      have hyB : ‖y‖ ≤ ‖x‖ + ‖y‖ := by linarith
      have hx_sq : ‖x‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by nlinarith
      have hy_sq : ‖y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by nlinarith
      have hxy_sq : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
        nlinarith [norm_nonneg (x + y)]
      nlinarith

theorem list_sum_mem_addSubgroup
    {M : Type*} [AddCommGroup M]
    (p : AddSubgroup M) (z : List M) (hz : ∀ x ∈ z, x ∈ p) :
    z.sum ∈ p := by
  induction z with
  | nil => simp
  | cons x z ih =>
      rw [List.sum_cons]
      exact p.add_mem (hz x (by simp))
        (ih (fun y hy => hz y (by simp [hy])))

omit [Nontrivial A] in
theorem norm_list_sum_le (z : List A) :
    ‖z.sum‖ ≤ (z.map norm).sum := by
  induction z with
  | nil => simp
  | cons x z ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (norm_add_le x z.sum).trans (add_le_add le_rfl ih)

/-- Quantitative first-order product formula for a finite list of
skew-adjoint generators. -/
theorem norm_list_exp_product_sub_exp_sum_le
    (z : List A) (hz : ∀ x ∈ z, x ∈ skewAdjoint A)
    (t : ℝ) (hsmall : |t| * (z.map norm).sum ≤ 1) :
    ‖(z.map fun x => exp (t • x)).prod - exp (t • z.sum)‖ ≤
      3 * z.length * (z.map norm).sum ^ 2 * |t| ^ 2 := by
  induction z with
  | nil => simp
  | cons x z ih =>
      have hx : x ∈ skewAdjoint A := hz x (by simp)
      have hz' : ∀ y ∈ z, y ∈ skewAdjoint A := by
        intro y hy
        exact hz y (by simp [hy])
      have hsum_skew : z.sum ∈ skewAdjoint A := by
        exact list_sum_mem_addSubgroup (skewAdjoint A) z hz'
      have hnorm_sum : ‖z.sum‖ ≤ (z.map norm).sum := by
        exact norm_list_sum_le z
      have htail_nonneg : 0 ≤ (z.map norm).sum := by
        exact List.sum_nonneg (by simp)
      have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
      have ht_nonneg : 0 ≤ |t| := abs_nonneg _
      have htail_small : |t| * (z.map norm).sum ≤ 1 := by
        calc
          |t| * (z.map norm).sum ≤ |t| * (‖x‖ + (z.map norm).sum) := by
            exact mul_le_mul_of_nonneg_left (by linarith) ht_nonneg
          _ ≤ 1 := by simpa using hsmall
      have hpair_small : |t| * (‖x‖ + ‖z.sum‖) ≤ 1 := by
        calc
          |t| * (‖x‖ + ‖z.sum‖) ≤
              |t| * (‖x‖ + (z.map norm).sum) := by gcongr
          _ ≤ 1 := by simpa using hsmall
      have hih := ih hz' htail_small
      have hpair := norm_exp_mul_exp_sub_exp_add_le
        x z.sum hx hsum_skew t hpair_small
      have hsplit :
          exp (t • x) * (z.map fun y => exp (t • y)).prod -
              exp (t • (x + z.sum)) =
            exp (t • x) *
                ((z.map fun y => exp (t • y)).prod - exp (t • z.sum)) +
              (exp (t • x) * exp (t • z.sum) -
                exp (t • (x + z.sum))) := by
        noncomm_ring
      let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [hsplit]
      calc
        ‖exp (t • x) *
              ((z.map fun y => exp (t • y)).prod - exp (t • z.sum)) +
            (exp (t • x) * exp (t • z.sum) -
              exp (t • (x + z.sum)))‖
            ≤ ‖exp (t • x) *
                ((z.map fun y => exp (t • y)).prod - exp (t • z.sum))‖ +
              ‖exp (t • x) * exp (t • z.sum) -
                exp (t • (x + z.sum))‖ := norm_add_le _ _
        _ = ‖(z.map fun y => exp (t • y)).prod - exp (t • z.sum)‖ +
              ‖exp (t • x) * exp (t • z.sum) -
                exp (t • (x + z.sum))‖ := by
              rw [CStarRing.norm_mem_unitary_mul _
                (exp_mem_unitary_of_mem_skewAdjoint
                  (skewAdjoint.smul_mem t hx))]
        _ ≤ 3 * z.length * (z.map norm).sum ^ 2 * |t| ^ 2 +
              3 * (‖x‖ + ‖z.sum‖) ^ 2 * |t| ^ 2 := add_le_add hih hpair
        _ ≤ 3 * (List.cons x z).length *
              ((List.cons x z).map norm).sum ^ 2 * |t| ^ 2 := by
          simp only [List.length_cons, List.map_cons, List.sum_cons]
          have hB_nonneg : 0 ≤ ‖x‖ + (z.map norm).sum := by positivity
          have htail_le : (z.map norm).sum ≤
              ‖x‖ + (z.map norm).sum := by linarith
          have htail_sq : (z.map norm).sum ^ 2 ≤
              (‖x‖ + (z.map norm).sum) ^ 2 :=
            (sq_le_sq₀ htail_nonneg hB_nonneg).2 htail_le
          have hpair_le : ‖x‖ + ‖z.sum‖ ≤
              ‖x‖ + (z.map norm).sum := add_le_add le_rfl hnorm_sum
          have hpair_sq : (‖x‖ + ‖z.sum‖) ^ 2 ≤
              (‖x‖ + (z.map norm).sum) ^ 2 :=
            (sq_le_sq₀ (by positivity) hB_nonneg).2 hpair_le
          have ht_sq_nonneg : 0 ≤ |t| ^ 2 := sq_nonneg _
          have htail_term :
              3 * (z.length : ℝ) * (z.map norm).sum ^ 2 * |t| ^ 2 ≤
                3 * (z.length : ℝ) *
                  (‖x‖ + (z.map norm).sum) ^ 2 * |t| ^ 2 := by gcongr
          have hpair_term :
              3 * (‖x‖ + ‖z.sum‖) ^ 2 * |t| ^ 2 ≤
                3 * (‖x‖ + (z.map norm).sum) ^ 2 * |t| ^ 2 := by gcongr
          calc
            3 * (z.length : ℝ) * (z.map norm).sum ^ 2 * |t| ^ 2 +
                3 * (‖x‖ + ‖z.sum‖) ^ 2 * |t| ^ 2 ≤
              3 * (z.length : ℝ) *
                  (‖x‖ + (z.map norm).sum) ^ 2 * |t| ^ 2 +
                3 * (‖x‖ + (z.map norm).sum) ^ 2 * |t| ^ 2 :=
                  add_le_add htail_term hpair_term
            _ = 3 * ((z.length + 1 : ℕ) : ℝ) *
                (‖x‖ + (z.map norm).sum) ^ 2 * |t| ^ 2 := by
                  push_cast
                  ring

omit [Nontrivial A] in
theorem list_exp_product_mem_unitary
    (z : List A) (hz : ∀ x ∈ z, x ∈ skewAdjoint A) (t : ℝ) :
    (z.map fun x => exp (t • x)).prod ∈ unitary A := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  induction z with
  | nil => simp
  | cons x z ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_mem
        (exp_mem_unitary_of_mem_skewAdjoint
          (skewAdjoint.smul_mem t (hz x (by simp))))
        (ih (fun y hy => hz y (by simp [hy])))

/-- `r` repetitions of the finite Lie product approximate the full-time
exponential with explicit `1/r` error. -/
theorem norm_list_exp_product_pow_sub_exp_sum_le
    (z : List A) (hz : ∀ x ∈ z, x ∈ skewAdjoint A)
    (t : ℝ) (r : ℕ) (hr : 0 < r)
    (hsmall : |t / (r : ℝ)| * (z.map norm).sum ≤ 1) :
    ‖(z.map fun x => exp ((t / (r : ℝ)) • x)).prod ^ r -
        exp (t • z.sum)‖ ≤
      3 * z.length * (z.map norm).sum ^ 2 * |t| ^ 2 / r := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let step : A :=
    (z.map fun x => exp ((t / (r : ℝ)) • x)).prod
  let exactStep : A := exp ((t / (r : ℝ)) • z.sum)
  have hstep_unitary : step ∈ unitary A := by
    exact list_exp_product_mem_unitary z hz (t / (r : ℝ))
  have hsum_skew : z.sum ∈ skewAdjoint A :=
    list_sum_mem_addSubgroup (skewAdjoint A) z hz
  have hexact_unitary : exactStep ∈ unitary A := by
    exact exp_mem_unitary_of_mem_skewAdjoint
      (skewAdjoint.smul_mem (t / (r : ℝ)) hsum_skew)
  have hone : ‖step - exactStep‖ ≤
      3 * z.length * (z.map norm).sum ^ 2 * |t / (r : ℝ)| ^ 2 := by
    exact norm_list_exp_product_sub_exp_sum_le z hz
      (t / (r : ℝ)) hsmall
  have hpower := unitary_pow_norm_sub_pow_le
    step exactStep hstep_unitary hexact_unitary r
  have hr_real : (0 : ℝ) < r := by exact_mod_cast hr
  have hexact_pow : exactStep ^ r = exp (t • z.sum) := by
    dsimp [exactStep]
    rw [exp_real_smul_pow]
    congr 2
    field_simp
  rw [← hexact_pow]
  calc
    ‖step ^ r - exactStep ^ r‖ ≤ (r : ℝ) * ‖step - exactStep‖ := hpower
    _ ≤ (r : ℝ) *
        (3 * z.length * (z.map norm).sum ^ 2 * |t / (r : ℝ)| ^ 2) := by
          gcongr
    _ = 3 * z.length * (z.map norm).sum ^ 2 * |t| ^ 2 / r := by
      rw [abs_div, abs_of_pos hr_real]
      field_simp

end GaloisForLFunctions.HTGeometry
