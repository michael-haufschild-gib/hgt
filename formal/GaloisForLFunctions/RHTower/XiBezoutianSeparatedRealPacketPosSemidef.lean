import GaloisForLFunctions.RHTower.XiCriticalKernelSeparatedRealPacketPositivity

/-!
# Separated real-packet positive semidefiniteness of the Bezoutian criterion matrices

From the two-sided logarithmic bounds on the real-ray logarithmic derivative of the centered
Xi function, this module derives geometric correlation decay of the critical
logarithmic-derivative kernel on multiplicatively separated real node packets, closes the
scaled Gershgorin argument, and concludes unconditional positive semidefiniteness of the
critical-kernel and theta tail first-moment Bezoutian matrices on every such packet — an
arbitrary-rank stratum of the matrix family whose positivity at all finite node systems of
the cofinal Euler half-plane is equivalent to the Riemann hypothesis.
-/

open Complex Real MeasureTheory Set
open scoped ComplexOrder

noncomputable section

namespace RHTower

/-! ## Correlation decay on multiplicatively separated nodes -/

private theorem log_div_self_antitone {a c : ℝ} (ha : Real.exp 1 ≤ a) (hac : a ≤ c) :
    Real.log c / c ≤ Real.log a / a := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hc0 : 0 < c := lt_of_lt_of_le ha0 hac
  have hla : 1 ≤ Real.log a := (Real.le_log_iff_exp_le ha0).mpr ha
  have hkey : a * Real.log c ≤ c * Real.log a := by
    have h1 : Real.log c - Real.log a ≤ c / a - 1 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < c / a from div_pos hc0 ha0)
      rwa [Real.log_div (ne_of_gt hc0) (ne_of_gt ha0)] at h
    have h2 : a * (Real.log c - Real.log a) ≤ c - a := by
      have h3 := mul_le_mul_of_nonneg_left h1 ha0.le
      have h4 : a * (c / a - 1) = c - a := by
        field_simp
      linarith [h4 ▸ h3]
    have h5 : c - a ≤ (c - a) * Real.log a := by
      nlinarith [hla, hac]
    nlinarith [h2, h5]
  rw [div_le_div_iff₀ hc0 ha0]
  linarith [hkey]

private theorem one_add_two_le_four_pow (d : ℕ) : (1 : ℝ) + 2 * d ≤ 4 ^ d := by
  induction d with
  | zero => norm_num
  | succ m ih =>
    have h4 : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
    have hstep : (4 : ℝ) ^ (m + 1) = 4 * 4 ^ m := by ring
    push_cast
    nlinarith [ih]

private theorem exp_one_le_packetBase : Real.exp 1 ≤ xiRayPacketBase := by
  have h1 := Real.exp_one_lt_d9
  have h2 := xiRayPacketBase_ge
  linarith

private theorem xiRayLogDeriv_pos_of_packetBase {u : ℝ} (hu : xiRayPacketBase ≤ u) :
    0 < xiRayLogDeriv u := by
  have hu0 : 0 < u := lt_of_lt_of_le (by linarith [xiRayPacketBase_ge]) hu
  have hlow := xiRayLogDeriv_ge (le_trans xiRayLowerBase_le_packetBase hu)
  have hlog : 1 ≤ Real.log u := by
    rw [Real.le_log_iff_exp_le hu0]
    linarith [exp_one_le_packetBase]
  linarith

private theorem packet_corr {u v : ℝ} (hu : xiRayPacketBase ≤ u) (hv : xiRayPacketBase ≤ v)
    {d : ℕ} (hgap : xiRayPacketBase ^ (2 * d) * u ≤ v) :
    (xiRayLogDeriv u + xiRayLogDeriv v) / (u + v)
      ≤ 32 * (2 / xiRayPacketBase) ^ d *
        (Real.sqrt (xiRayLogDeriv u / u) * Real.sqrt (xiRayLogDeriv v / v)) := by
  have hR256 := xiRayPacketBase_ge
  have hR0 : (0 : ℝ) < xiRayPacketBase := by linarith
  have hR1 : (1 : ℝ) ≤ xiRayPacketBase := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have huv : u ≤ v := by
    have hpow : (1 : ℝ) ≤ xiRayPacketBase ^ (2 * d) := one_le_pow₀ hR1
    nlinarith
  have hueexp : Real.exp 1 ≤ u := le_trans exp_one_le_packetBase hu
  have hru_le := xiRayLogDeriv_le (le_trans xiRayUpperBase_le_packetBase hu)
  have hru_ge := xiRayLogDeriv_ge (le_trans xiRayLowerBase_le_packetBase hu)
  have hrv_le := xiRayLogDeriv_le (le_trans xiRayUpperBase_le_packetBase hv)
  have hrv_ge := xiRayLogDeriv_ge (le_trans xiRayLowerBase_le_packetBase hv)
  have hlogu1 : 1 ≤ Real.log u := (Real.le_log_iff_exp_le hu0).mpr hueexp
  have hlogv1 : 1 ≤ Real.log v :=
    (Real.le_log_iff_exp_le hv0).mpr (le_trans hueexp huv)
  have hloguv : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
  set q : ℝ := 2 / xiRayPacketBase with hqdef
  have hq0 : 0 < q := div_pos (by norm_num) hR0
  -- the log-ratio contraction
  have hkey : Real.log v / v ≤ q ^ (2 * d) * (Real.log u / u) := by
    have hRu0 : (0 : ℝ) < xiRayPacketBase ^ (2 * d) * u :=
      mul_pos (pow_pos hR0 _) hu0
    have hRue : Real.exp 1 ≤ xiRayPacketBase ^ (2 * d) * u := by
      have hpow : (1 : ℝ) ≤ xiRayPacketBase ^ (2 * d) := one_le_pow₀ hR1
      nlinarith
    have step1 : Real.log v / v
        ≤ Real.log (xiRayPacketBase ^ (2 * d) * u) / (xiRayPacketBase ^ (2 * d) * u) :=
      log_div_self_antitone hRue hgap
    have step2 : Real.log (xiRayPacketBase ^ (2 * d) * u)
        = 2 * d * Real.log xiRayPacketBase + Real.log u := by
      rw [Real.log_mul (ne_of_gt (pow_pos hR0 _)) (ne_of_gt hu0), Real.log_pow]
      push_cast
      ring
    have hlogR : Real.log xiRayPacketBase ≤ Real.log u := Real.log_le_log hR0 hu
    have hlogR0 : 0 ≤ Real.log xiRayPacketBase := Real.log_nonneg hR1
    have step3 : 2 * d * Real.log xiRayPacketBase + Real.log u
        ≤ 4 ^ d * Real.log u := by
      have h1 : 2 * (d : ℝ) * Real.log xiRayPacketBase ≤ 2 * d * Real.log u := by
        apply mul_le_mul_of_nonneg_left hlogR
        positivity
      have h2 : (1 + 2 * (d : ℝ)) * Real.log u ≤ 4 ^ d * Real.log u := by
        apply mul_le_mul_of_nonneg_right (one_add_two_le_four_pow d)
        linarith
      nlinarith
    have step4 : Real.log (xiRayPacketBase ^ (2 * d) * u) / (xiRayPacketBase ^ (2 * d) * u)
        ≤ (4 ^ d * Real.log u) / (xiRayPacketBase ^ (2 * d) * u) := by
      apply div_le_div_of_nonneg_right _ hRu0.le
      rw [step2]
      exact step3
    have step5 : (4 ^ d * Real.log u) / (xiRayPacketBase ^ (2 * d) * u)
        = q ^ (2 * d) * (Real.log u / u) := by
      rw [hqdef, div_pow, show ((2 : ℝ)) ^ (2 * d) = 4 ^ d by
        rw [pow_mul]
        norm_num]
      field_simp
    calc Real.log v / v
        ≤ Real.log (xiRayPacketBase ^ (2 * d) * u) / (xiRayPacketBase ^ (2 * d) * u) := step1
      _ ≤ (4 ^ d * Real.log u) / (xiRayPacketBase ^ (2 * d) * u) := step4
      _ = q ^ (2 * d) * (Real.log u / u) := step5
  set A : ℝ := Real.log v / v with hAdef
  set B : ℝ := Real.log u / u with hBdef
  have hA0 : 0 ≤ A := div_nonneg (by linarith) hv0.le
  have hB0 : 0 ≤ B := div_nonneg (by linarith) hu0.le
  -- the square-root form of the contraction
  have hsqrt : A ≤ q ^ d * Real.sqrt (B * A) := by
    have h1 : A * A ≤ (q ^ (2 * d) * B) * A := mul_le_mul_of_nonneg_right hkey hA0
    have h2 : Real.sqrt (A * A) ≤ Real.sqrt ((q ^ (2 * d) * B) * A) :=
      Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt (A * A) = A := Real.sqrt_mul_self hA0
    have h4 : (q ^ (2 * d) * B) * A = (q ^ d) ^ 2 * (B * A) := by
      rw [show 2 * d = d * 2 from Nat.mul_comm 2 d, pow_mul]
      ring
    have h5 : Real.sqrt ((q ^ d) ^ 2 * (B * A))
        = q ^ d * Real.sqrt (B * A) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hq0.le _)]
    calc A = Real.sqrt (A * A) := h3.symm
      _ ≤ Real.sqrt ((q ^ (2 * d) * B) * A) := h2
      _ = Real.sqrt ((q ^ d) ^ 2 * (B * A)) := by rw [h4]
      _ = q ^ d * Real.sqrt (B * A) := h5
  -- kernel numerator and diagonal comparison
  have hKnum : (xiRayLogDeriv u + xiRayLogDeriv v) / (u + v) ≤ 4 * Real.log v / v := by
    have hnum : xiRayLogDeriv u + xiRayLogDeriv v ≤ 4 * Real.log v := by
      have h1 : xiRayLogDeriv u ≤ Real.log v + 1 := by linarith
      have h2 : xiRayLogDeriv v ≤ Real.log v + 1 := by linarith
      linarith
    have hnum0 : 0 ≤ xiRayLogDeriv u + xiRayLogDeriv v := by
      have := xiRayLogDeriv_pos_of_packetBase hu
      have := xiRayLogDeriv_pos_of_packetBase hv
      linarith
    calc (xiRayLogDeriv u + xiRayLogDeriv v) / (u + v)
        ≤ (xiRayLogDeriv u + xiRayLogDeriv v) / v := by
          apply div_le_div_of_nonneg_left hnum0 hv0
          linarith
      _ ≤ (4 * Real.log v) / v := div_le_div_of_nonneg_right hnum hv0.le
      _ = 4 * Real.log v / v := by ring
  -- diagonal square roots dominate the (1/8)-scaled log data
  have hDu : B / 8 ≤ xiRayLogDeriv u / u := by
    have h1 : Real.log u / 8 / u ≤ xiRayLogDeriv u / u :=
      div_le_div_of_nonneg_right hru_ge hu0.le
    have h2 : B / 8 = Real.log u / 8 / u := by
      rw [hBdef]
      ring
    rw [h2]
    exact h1
  have hDv : A / 8 ≤ xiRayLogDeriv v / v := by
    have h1 : Real.log v / 8 / v ≤ xiRayLogDeriv v / v :=
      div_le_div_of_nonneg_right hrv_ge hv0.le
    have h2 : A / 8 = Real.log v / 8 / v := by
      rw [hAdef]
      ring
    rw [h2]
    exact h1
  have hsq8 : Real.sqrt (B / 8) * Real.sqrt (A / 8) = Real.sqrt (B * A) / 8 := by
    rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ B / 8)]
    have h1 : B / 8 * (A / 8) = B * A * (1 / 64) := by ring
    rw [h1, Real.sqrt_mul (mul_nonneg hB0 hA0),
      show (1 : ℝ) / 64 = (1 / 8) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 8)]
    ring
  have h3 : Real.sqrt (B / 8) * Real.sqrt (A / 8)
      ≤ Real.sqrt (xiRayLogDeriv u / u) * Real.sqrt (xiRayLogDeriv v / v) :=
    mul_le_mul (Real.sqrt_le_sqrt hDu) (Real.sqrt_le_sqrt hDv)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc (xiRayLogDeriv u + xiRayLogDeriv v) / (u + v)
      ≤ 4 * Real.log v / v := hKnum
    _ = 4 * A := by rw [hAdef]; ring
    _ ≤ 4 * (q ^ d * Real.sqrt (B * A)) := by
        linarith [mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 4)]
    _ = 32 * q ^ d * (Real.sqrt (B * A) / 8) := by ring
    _ = 32 * q ^ d * (Real.sqrt (B / 8) * Real.sqrt (A / 8)) := by rw [hsq8]
    _ ≤ 32 * q ^ d *
          (Real.sqrt (xiRayLogDeriv u / u) * Real.sqrt (xiRayLogDeriv v / v)) := by
        exact mul_le_mul_of_nonneg_left h3
          (mul_nonneg (by norm_num) (pow_nonneg hq0.le d))

end RHTower

namespace RHTower

/-! ## Separated-packet positivity of the real critical kernel -/

private theorem diag_eq {u : ℝ} (hu : u ≠ 0) :
    (xiRayLogDeriv u + xiRayLogDeriv u) / (u + u) = xiRayLogDeriv u / u := by
  rw [div_eq_div_iff (by simpa [two_mul] using mul_ne_zero (two_ne_zero) hu) hu]
  ring

private theorem geom_row_sum_le' {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n i : ℕ) :
    ∑ j ∈ (Finset.range n).erase i, q ^ Nat.dist i j ≤ 2 * (q / (1 - q)) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have htail : ∀ m : ℕ, ∑ k ∈ Finset.range m, q ^ (k + 1) ≤ q / (1 - q) := by
    intro m
    have hgeom : ∑ k ∈ Finset.range m, q ^ k ≤ 1 / (1 - q) := by
      rw [geom_sum_eq (ne_of_lt hq1) m,
        show (q ^ m - 1) / (q - 1) = (1 - q ^ m) / (1 - q) by
          rw [← neg_div_neg_eq]; ring_nf]
      have h0 : (0 : ℝ) ≤ q ^ m := by positivity
      have hnum : (1 : ℝ) - q ^ m ≤ 1 := by linarith
      have := mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr h1q.le)
      simpa [div_eq_mul_inv] using this
    have hstep : ∑ k ∈ Finset.range m, q ^ (k + 1) =
        q * ∑ k ∈ Finset.range m, q ^ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [pow_succ]; ring
    rw [hstep]
    calc q * ∑ k ∈ Finset.range m, q ^ k ≤ q * (1 / (1 - q)) :=
          mul_le_mul_of_nonneg_left hgeom hq0
      _ = q / (1 - q) := by ring
  have hsplit : (Finset.range n).erase i =
      Finset.range (min i n) ∪ Finset.Ico (i + 1) n := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico,
      lt_min_iff]
    omega
  have hdisj : Disjoint (Finset.range (min i n)) (Finset.Ico (i + 1) n) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_range, lt_min_iff] at hj
    simp only [Finset.mem_Ico] at hj'
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hleft : ∑ j ∈ Finset.range (min i n), q ^ Nat.dist i j ≤ q / (1 - q) := by
    have hcongr : ∑ j ∈ Finset.range (min i n), q ^ Nat.dist i j =
        ∑ j ∈ Finset.range (min i n), q ^ (i - j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range, lt_min_iff] at hj
      rw [Nat.dist_eq_sub_of_le_right (by omega)]
    rw [hcongr]
    calc ∑ j ∈ Finset.range (min i n), q ^ (i - j)
        ≤ ∑ j ∈ Finset.range (min i n), q ^ (min i n - 1 - j + 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          simp only [Finset.mem_range, lt_min_iff] at hj
          exact pow_le_pow_of_le_one hq0 hq1.le (by omega)
      _ = ∑ k ∈ Finset.range (min i n), q ^ (k + 1) :=
          Finset.sum_range_reflect (fun k => q ^ (k + 1)) (min i n)
      _ ≤ q / (1 - q) := htail _
  have hright : ∑ j ∈ Finset.Ico (i + 1) n, q ^ Nat.dist i j ≤ q / (1 - q) := by
    have hcongr : ∑ j ∈ Finset.Ico (i + 1) n, q ^ Nat.dist i j =
        ∑ k ∈ Finset.range (n - (i + 1)), q ^ (k + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.dist_eq_sub_of_le (by omega)]
      congr 1
      omega
    rw [hcongr]
    exact htail _
  linarith

/-- **Separated real-packet positivity of the critical logarithmic-derivative kernel.**
For every real node packet with base at least `xiRayPacketBase` and consecutive
multiplicative ratio at least `xiRayPacketBase ^ 2`, every length, and every real
coefficient vector, the quadratic form of the real critical kernel `(L(x)+L(y))/(x+y)`
is nonnegative.  Unconditional. -/
theorem xiRayCriticalKernel_separatedPacket_quadraticForm_nonneg
    {x : ℕ → ℝ} (hbase : xiRayPacketBase ≤ x 0)
    (hstep : ∀ m, xiRayPacketBase ^ 2 * x m ≤ x (m + 1)) (n : ℕ) (a : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      a i * a j * ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) := by
  have hR256 := xiRayPacketBase_ge
  have hR0 : (0 : ℝ) < xiRayPacketBase := by linarith
  have hR1 : (1 : ℝ) ≤ xiRayPacketBase := by linarith
  have hgap : ∀ i j : ℕ, i ≤ j → xiRayPacketBase ^ (2 * (j - i)) * x i ≤ x j := by
    intro i j hij
    induction j with
    | zero =>
      have h0 : i = 0 := Nat.le_zero.mp hij
      subst h0
      simp
    | succ m ih =>
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · have him : i ≤ m := by omega
        have h1 := ih him
        have h2 := hstep m
        have hcast : 2 * (m + 1 - i) = 2 * (m - i) + 2 := by omega
        rw [hcast, pow_add]
        have hpow0 : (0 : ℝ) ≤ xiRayPacketBase ^ 2 := sq_nonneg _
        calc xiRayPacketBase ^ (2 * (m - i)) * xiRayPacketBase ^ 2 * x i
            = xiRayPacketBase ^ 2 * (xiRayPacketBase ^ (2 * (m - i)) * x i) := by ring
          _ ≤ xiRayPacketBase ^ 2 * x m := mul_le_mul_of_nonneg_left h1 hpow0
          _ ≤ x (m + 1) := h2
      · have h0 : i = m + 1 := by omega
        subst h0
        simp
  have hone : ∀ i : ℕ, xiRayPacketBase ≤ x i := by
    intro i
    have h := hgap 0 i (Nat.zero_le i)
    have hpow : (1 : ℝ) ≤ xiRayPacketBase ^ (2 * (i - 0)) := one_le_pow₀ hR1
    have hx0pos : (0 : ℝ) < x 0 := lt_of_lt_of_le hR0 hbase
    calc xiRayPacketBase ≤ x 0 := hbase
      _ = 1 * x 0 := (one_mul _).symm
      _ ≤ xiRayPacketBase ^ (2 * (i - 0)) * x 0 :=
          mul_le_mul_of_nonneg_right hpow hx0pos.le
      _ ≤ x i := h
  have hxpos : ∀ i : ℕ, (0 : ℝ) < x i := fun i => lt_of_lt_of_le hR0 (hone i)
  have hrpos : ∀ i : ℕ, 0 < xiRayLogDeriv (x i) := fun i =>
    xiRayLogDeriv_pos_of_packetBase (hone i)
  have hKnn : ∀ i j : ℕ, 0 ≤ (xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j) :=
    fun i j => div_nonneg (by linarith [hrpos i, hrpos j])
      (by linarith [hxpos i, hxpos j])
  have hq0 : (0 : ℝ) < 2 / xiRayPacketBase := div_pos (by norm_num) hR0
  have hq128 : 2 / xiRayPacketBase ≤ 1 / 128 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 256) hR256
    calc 2 / xiRayPacketBase ≤ 2 / 256 := h
      _ = 1 / 128 := by norm_num
  have hq1 : 2 / xiRayPacketBase < 1 := by linarith
  have h1q : (0 : ℝ) < 1 - 2 / xiRayPacketBase := by linarith
  have hqK : 32 * (2 * (2 / xiRayPacketBase / (1 - 2 / xiRayPacketBase))) ≤ 1 := by
    have h2 : 32 * (2 * (2 / xiRayPacketBase / (1 - 2 / xiRayPacketBase)))
        = 64 * (2 / xiRayPacketBase) / (1 - 2 / xiRayPacketBase) := by ring
    rw [h2, div_le_one h1q]
    linarith
  have hdiag : ∀ i : ℕ, (xiRayLogDeriv (x i) + xiRayLogDeriv (x i)) / (x i + x i)
      = xiRayLogDeriv (x i) / x i := fun i => diag_eq (ne_of_gt (hxpos i))
  have hcorr : ∀ i j : ℕ, i < j →
      (xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)
        ≤ 32 * (2 / xiRayPacketBase) ^ (j - i) *
          (Real.sqrt ((xiRayLogDeriv (x i) + xiRayLogDeriv (x i)) / (x i + x i)) *
            Real.sqrt ((xiRayLogDeriv (x j) + xiRayLogDeriv (x j)) / (x j + x j))) := by
    intro i j hij
    have h := packet_corr (hone i) (hone j) (d := j - i) (hgap i j hij.le)
    rw [hdiag i, hdiag j]
    exact h
  set b : ℕ → ℝ := fun i => |a i| *
    Real.sqrt ((xiRayLogDeriv (x i) + xiRayLogDeriv (x i)) / (x i + x i)) with hbdef
  have hbsq : ∀ i : ℕ, b i ^ 2 = a i ^ 2 *
      ((xiRayLogDeriv (x i) + xiRayLogDeriv (x i)) / (x i + x i)) := by
    intro i
    rw [hbdef]
    have h := hKnn i i
    rw [mul_pow, sq_abs, Real.sq_sqrt h]
  have hpair : ∀ i j : ℕ, i ≠ j →
      -(32 * (2 / xiRayPacketBase) ^ Nat.dist i j * ((b i ^ 2 + b j ^ 2) / 2)) ≤
        a i * a j * ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) := by
    have hmain : ∀ i j : ℕ, i < j →
        -(32 * (2 / xiRayPacketBase) ^ Nat.dist i j * ((b i ^ 2 + b j ^ 2) / 2)) ≤
          a i * a j * ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) := by
      intro i j hij
      have hk := hcorr i j hij
      have hknn := hKnn i j
      have hdist : Nat.dist i j = j - i := Nat.dist_eq_sub_of_le hij.le
      have habs : -(|a i| * |a j| *
          ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j))) ≤
          a i * a j * ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) := by
        have h1 : -(|a i| * |a j|) ≤ a i * a j := by
          rw [← abs_mul]
          exact neg_abs_le _
        have h2 := mul_le_mul_of_nonneg_right h1 hknn
        calc -(|a i| * |a j| *
            ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)))
            = -(|a i| * |a j|) *
                ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) := by ring
          _ ≤ a i * a j *
                ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) := h2
      have hup : |a i| * |a j| *
          ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) ≤
          32 * (2 / xiRayPacketBase) ^ (j - i) * (b i * b j) := by
        have h2 := mul_le_mul_of_nonneg_left hk
          (show (0 : ℝ) ≤ |a i| * |a j| by positivity)
        calc |a i| * |a j| *
            ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j))
            ≤ |a i| * |a j| * (32 * (2 / xiRayPacketBase) ^ (j - i) *
                (Real.sqrt ((xiRayLogDeriv (x i) + xiRayLogDeriv (x i)) / (x i + x i)) *
                  Real.sqrt ((xiRayLogDeriv (x j) + xiRayLogDeriv (x j)) / (x j + x j)))) :=
              h2
          _ = 32 * (2 / xiRayPacketBase) ^ (j - i) * (b i * b j) := by
              rw [hbdef]
              ring
      have hamgm : b i * b j ≤ (b i ^ 2 + b j ^ 2) / 2 := by
        nlinarith [sq_nonneg (b i - b j)]
      have hKq : (0 : ℝ) ≤ 32 * (2 / xiRayPacketBase) ^ (j - i) :=
        mul_nonneg (by norm_num) (pow_nonneg hq0.le _)
      rw [hdist]
      have h8 := mul_le_mul_of_nonneg_left hamgm hKq
      calc -(32 * (2 / xiRayPacketBase) ^ (j - i) * ((b i ^ 2 + b j ^ 2) / 2))
          ≤ -(32 * (2 / xiRayPacketBase) ^ (j - i) * (b i * b j)) := by linarith
        _ ≤ -(|a i| * |a j| *
              ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j))) := by
            linarith
        _ ≤ a i * a j *
              ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) := habs
    intro i j hij
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact hmain i j hlt
    · have hlt : j < i := by omega
      have h := hmain j i hlt
      rw [Nat.dist_comm]
      calc -(32 * (2 / xiRayPacketBase) ^ Nat.dist j i * ((b i ^ 2 + b j ^ 2) / 2))
          = -(32 * (2 / xiRayPacketBase) ^ Nat.dist j i * ((b j ^ 2 + b i ^ 2) / 2)) := by
            ring
        _ ≤ a j * a i * ((xiRayLogDeriv (x j) + xiRayLogDeriv (x i)) / (x j + x i)) := h
        _ = a i * a j * ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) := by
            rw [add_comm (xiRayLogDeriv (x j)), add_comm (x j)]
            ring
  have hrow : ∀ i : ℕ,
      ∑ j ∈ (Finset.range n).erase i,
        32 * (2 / xiRayPacketBase) ^ Nat.dist i j ≤ 1 := by
    intro i
    rw [← Finset.mul_sum]
    have hg := geom_row_sum_le' hq0.le hq1 n i
    have h2 : (32 : ℝ) * (2 * (2 / xiRayPacketBase / (1 - 2 / xiRayPacketBase))) ≤ 1 := hqK
    calc (32 : ℝ) * ∑ j ∈ (Finset.range n).erase i,
          (2 / xiRayPacketBase) ^ Nat.dist i j
        ≤ 32 * (2 * (2 / xiRayPacketBase / (1 - 2 / xiRayPacketBase))) :=
          mul_le_mul_of_nonneg_left hg (by norm_num)
      _ ≤ 1 := h2
  have hexpand : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      a i * a j * ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) =
      ∑ i ∈ Finset.range n, (b i ^ 2 +
        ∑ j ∈ (Finset.range n).erase i,
          a i * a j * ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j))) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.add_sum_erase _ _ hi]
    congr 1
    rw [hbsq i]
    ring
  rw [hexpand]
  have hlower : ∀ i ∈ Finset.range n,
      b i ^ 2 - (∑ j ∈ (Finset.range n).erase i,
          32 * (2 / xiRayPacketBase) ^ Nat.dist i j * ((b i ^ 2 + b j ^ 2) / 2)) ≤
        b i ^ 2 + ∑ j ∈ (Finset.range n).erase i,
          a i * a j * ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)) := by
    intro i _
    have h := Finset.sum_le_sum (s := (Finset.range n).erase i)
      (f := fun j => -(32 * (2 / xiRayPacketBase) ^ Nat.dist i j *
        ((b i ^ 2 + b j ^ 2) / 2)))
      (g := fun j => a i * a j *
        ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j)))
      (fun j hj => hpair i j (by
        simp only [Finset.mem_erase] at hj
        exact fun hij => hj.1 (hij.symm)))
    rw [Finset.sum_neg_distrib] at h
    linarith
  have hswap : ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
      32 * (2 / xiRayPacketBase) ^ Nat.dist i j * b j ^ 2 =
      ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
        32 * (2 / xiRayPacketBase) ^ Nat.dist i j * b i ^ 2 := by
    rw [Finset.sum_comm' (t' := Finset.range n)
      (s' := fun j => (Finset.range n).erase j)
      (by
        intro i j
        simp only [Finset.mem_erase, Finset.mem_range]
        omega)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.dist_comm]
  have hW : ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
      32 * (2 / xiRayPacketBase) ^ Nat.dist i j *
        ((b i ^ 2 + b j ^ 2) / 2) ≤ ∑ i ∈ Finset.range n, b i ^ 2 := by
    have hsplit : ∀ i, ∑ j ∈ (Finset.range n).erase i,
        32 * (2 / xiRayPacketBase) ^ Nat.dist i j *
          ((b i ^ 2 + b j ^ 2) / 2) =
        (∑ j ∈ (Finset.range n).erase i,
          32 * (2 / xiRayPacketBase) ^ Nat.dist i j * b i ^ 2) / 2 +
        (∑ j ∈ (Finset.range n).erase i,
          32 * (2 / xiRayPacketBase) ^ Nat.dist i j * b j ^ 2) / 2 := by
      intro i
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hA : ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
        32 * (2 / xiRayPacketBase) ^ Nat.dist i j * b i ^ 2 ≤
        ∑ i ∈ Finset.range n, b i ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : ∑ j ∈ (Finset.range n).erase i,
          32 * (2 / xiRayPacketBase) ^ Nat.dist i j * b i ^ 2 =
          (∑ j ∈ (Finset.range n).erase i,
            32 * (2 / xiRayPacketBase) ^ Nat.dist i j) * b i ^ 2 := by
        rw [Finset.sum_mul]
      rw [h1]
      have h2 : (0 : ℝ) ≤ b i ^ 2 := sq_nonneg _
      calc (∑ j ∈ (Finset.range n).erase i,
            32 * (2 / xiRayPacketBase) ^ Nat.dist i j) * b i ^ 2
          ≤ 1 * b i ^ 2 := mul_le_mul_of_nonneg_right (hrow i) h2
        _ = b i ^ 2 := one_mul _
    calc ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
          32 * (2 / xiRayPacketBase) ^ Nat.dist i j *
            ((b i ^ 2 + b j ^ 2) / 2)
        = (∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
            32 * (2 / xiRayPacketBase) ^ Nat.dist i j * b i ^ 2) / 2 +
          (∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
            32 * (2 / xiRayPacketBase) ^ Nat.dist i j * b j ^ 2) / 2 := by
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => hsplit i
      _ = ∑ i ∈ Finset.range n, ∑ j ∈ (Finset.range n).erase i,
            32 * (2 / xiRayPacketBase) ^ Nat.dist i j * b i ^ 2 := by
          rw [hswap]
          ring
      _ ≤ ∑ i ∈ Finset.range n, b i ^ 2 := hA
  have hfinal : ∑ i ∈ Finset.range n, (b i ^ 2 -
      ∑ j ∈ (Finset.range n).erase i,
        32 * (2 / xiRayPacketBase) ^ Nat.dist i j * ((b i ^ 2 + b j ^ 2) / 2)) ≤
      ∑ i ∈ Finset.range n, (b i ^ 2 +
        ∑ j ∈ (Finset.range n).erase i,
          a i * a j * ((xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j))) :=
    Finset.sum_le_sum hlower
  have hleft : 0 ≤ ∑ i ∈ Finset.range n, (b i ^ 2 -
      ∑ j ∈ (Finset.range n).erase i,
        32 * (2 / xiRayPacketBase) ^ Nat.dist i j * ((b i ^ 2 + b j ^ 2) / 2)) := by
    rw [Finset.sum_sub_distrib]
    have h1 := hW
    linarith
  linarith

end RHTower

namespace RHTower

/-! ## Matrix positivity: the critical-kernel and Bezoutian strata -/

/-- The critical logarithmic-derivative kernel at real nodes is the real Laplace-quotient
kernel of the theta-cusp source. -/
theorem criticalLogDerivKernel_ofReal_eq {u v : ℝ} :
    criticalLogDerivKernel (u : ℂ) (v : ℂ)
      = (((xiRayLogDeriv u + xiRayLogDeriv v) / (u + v) : ℝ) : ℂ) := by
  unfold criticalLogDerivKernel
  rw [logDeriv_xiCent_ofReal u, logDeriv_xiCent_ofReal v, Complex.conj_ofReal,
    Complex.conj_ofReal, ← Complex.ofReal_add, ← Complex.ofReal_add, Complex.ofReal_div]

private theorem packet_le {x : ℕ → ℝ} (hbase : xiRayPacketBase ≤ x 0)
    (hstep : ∀ m, xiRayPacketBase ^ 2 * x m ≤ x (m + 1)) :
    ∀ i : ℕ, xiRayPacketBase ≤ x i := by
  have hR256 := xiRayPacketBase_ge
  have hR0 : (0 : ℝ) < xiRayPacketBase := by linarith
  intro i
  induction i with
  | zero => exact hbase
  | succ m ih =>
    have h1 := hstep m
    have hxm : 0 < x m := lt_of_lt_of_le hR0 ih
    have hsq : xiRayPacketBase ≤ xiRayPacketBase ^ 2 := by nlinarith
    have h2 : xiRayPacketBase ≤ xiRayPacketBase ^ 2 * x m := by nlinarith
    linarith

/-- **Separated real packets give positive semidefinite critical-kernel matrices.**
An arbitrary-rank unconditional positivity stratum of the RH-critical kernel family. -/
theorem posSemidef_criticalLogDerivKernel_separatedRealPacket
    {x : ℕ → ℝ} (hbase : xiRayPacketBase ≤ x 0)
    (hstep : ∀ m, xiRayPacketBase ^ 2 * x m ≤ x (m + 1)) (n : ℕ) :
    (Matrix.of fun j k : Fin n =>
      criticalLogDerivKernel ((x j : ℝ) : ℂ) ((x k : ℝ) : ℂ)).PosSemidef := by
  classical
  set KR : ℕ → ℕ → ℝ := fun i j =>
    (xiRayLogDeriv (x i) + xiRayLogDeriv (x j)) / (x i + x j) with hKRdef
  have hentry : ∀ j k : Fin n,
      criticalLogDerivKernel ((x j : ℝ) : ℂ) ((x k : ℝ) : ℂ)
        = ((KR (j : ℕ) (k : ℕ) : ℝ) : ℂ) :=
    fun j k => criticalLogDerivKernel_ofReal_eq
  have hKRsymm : ∀ i j : ℕ, KR i j = KR j i := by
    intro i j
    rw [hKRdef]
    dsimp only
    rw [add_comm (xiRayLogDeriv (x i)), add_comm (x i)]
  have hfin : ∀ c : ℕ → ℝ,
      0 ≤ ∑ j : Fin n, ∑ k : Fin n, c (j : ℕ) * c (k : ℕ) * KR (j : ℕ) (k : ℕ) := by
    intro c
    have hcore := xiRayCriticalKernel_separatedPacket_quadraticForm_nonneg hbase hstep n c
    have houter : (∑ j : Fin n, ∑ k : Fin n, c (j : ℕ) * c (k : ℕ) * KR (j : ℕ) (k : ℕ))
        = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, c i * c j * KR i j := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun i => ∑ j ∈ Finset.range n, c i * c j * KR i j) n]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun k => c (j : ℕ) * c k * KR (j : ℕ) k) n]
    rw [houter]
    exact hcore
  have hherm : (Matrix.of fun j k : Fin n =>
      criticalLogDerivKernel ((x j : ℝ) : ℂ) ((x k : ℝ) : ℂ)).IsHermitian := by
    ext j k
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, hentry, hentry,
      RCLike.star_def, Complex.conj_ofReal]
    exact congrArg _ (hKRsymm (k : ℕ) (j : ℕ))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun cv => ?_)
  set cre : ℕ → ℝ := fun i => if h : i < n then (cv ⟨i, h⟩).re else 0 with hcre
  set cim : ℕ → ℝ := fun i => if h : i < n then (cv ⟨i, h⟩).im else 0 with hcim
  have hcre_eq : ∀ j : Fin n, cre (j : ℕ) = (cv j).re := by
    intro j
    rw [hcre]
    dsimp only
    rw [dif_pos j.isLt]
  have hcim_eq : ∀ j : Fin n, cim (j : ℕ) = (cv j).im := by
    intro j
    rw [hcim]
    dsimp only
    rw [dif_pos j.isLt]
  have hval : star cv ⬝ᵥ (Matrix.of fun j k : Fin n =>
      criticalLogDerivKernel ((x j : ℝ) : ℂ) ((x k : ℝ) : ℂ)).mulVec cv
      = ∑ j : Fin n, ∑ k : Fin n,
          ((KR (j : ℕ) (k : ℕ) : ℝ) : ℂ) * ((starRingEnd ℂ) (cv j) * cv k) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hentry]
    ring
  rw [hval]
  have hre : (∑ j : Fin n, ∑ k : Fin n,
      ((KR (j : ℕ) (k : ℕ) : ℝ) : ℂ) * ((starRingEnd ℂ) (cv j) * cv k)).re
      = (∑ j : Fin n, ∑ k : Fin n, cre (j : ℕ) * cre (k : ℕ) * KR (j : ℕ) (k : ℕ))
        + ∑ j : Fin n, ∑ k : Fin n, cim (j : ℕ) * cim (k : ℕ) * KR (j : ℕ) (k : ℕ) := by
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcre_eq, hcre_eq, hcim_eq, hcim_eq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have him : (∑ j : Fin n, ∑ k : Fin n,
      ((KR (j : ℕ) (k : ℕ) : ℝ) : ℂ) * ((starRingEnd ℂ) (cv j) * cv k)).im = 0 := by
    have hterm : ∀ j k : Fin n,
        (((KR (j : ℕ) (k : ℕ) : ℝ) : ℂ) * ((starRingEnd ℂ) (cv j) * cv k)).im
        = KR (j : ℕ) (k : ℕ) * ((cv j).re * (cv k).im - (cv j).im * (cv k).re) := by
      intro j k
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.conj_re, Complex.conj_im]
      ring
    have hstep1 : (∑ j : Fin n, ∑ k : Fin n,
        ((KR (j : ℕ) (k : ℕ) : ℝ) : ℂ) * ((starRingEnd ℂ) (cv j) * cv k)).im
        = ∑ j : Fin n, ∑ k : Fin n,
            KR (j : ℕ) (k : ℕ) * ((cv j).re * (cv k).im - (cv j).im * (cv k).re) := by
      rw [Complex.im_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.im_sum]
      exact Finset.sum_congr rfl fun k _ => hterm j k
    rw [hstep1]
    have hanti : ∀ j k : Fin n,
        KR (j : ℕ) (k : ℕ) * ((cv j).re * (cv k).im - (cv j).im * (cv k).re)
        = -(KR (k : ℕ) (j : ℕ) * ((cv k).re * (cv j).im - (cv k).im * (cv j).re)) := by
      intro j k
      rw [hKRsymm (j : ℕ) (k : ℕ)]
      ring
    have hS2 : (∑ j : Fin n, ∑ k : Fin n,
        KR (j : ℕ) (k : ℕ) * ((cv j).re * (cv k).im - (cv j).im * (cv k).re))
        = -(∑ j : Fin n, ∑ k : Fin n,
            KR (j : ℕ) (k : ℕ) * ((cv j).re * (cv k).im - (cv j).im * (cv k).re)) := by
      calc (∑ j : Fin n, ∑ k : Fin n,
          KR (j : ℕ) (k : ℕ) * ((cv j).re * (cv k).im - (cv j).im * (cv k).re))
          = ∑ k : Fin n, ∑ j : Fin n,
              KR (j : ℕ) (k : ℕ) * ((cv j).re * (cv k).im - (cv j).im * (cv k).re) :=
            Finset.sum_comm
        _ = ∑ k : Fin n, ∑ j : Fin n,
              -(KR (k : ℕ) (j : ℕ) * ((cv k).re * (cv j).im - (cv k).im * (cv j).re)) := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
            exact hanti j k
        _ = -(∑ k : Fin n, ∑ j : Fin n,
              KR (k : ℕ) (j : ℕ) * ((cv k).re * (cv j).im - (cv k).im * (cv j).re)) := by
            simp only [Finset.sum_neg_distrib]
    linarith [hS2]
  rw [Complex.le_def]
  constructor
  · rw [hre]
    simp only [Complex.zero_re]
    have h1 := hfin cre
    have h2 := hfin cim
    linarith
  · rw [him]
    simp only [Complex.zero_im]

/-- **Separated real packets give positive semidefinite Bezoutian matrices**: an
arbitrary-rank unconditional positivity stratum of the theta tail first-moment Bezoutian
family, whose positivity at all finite node systems of the cofinal Euler half-plane is
equivalent to the Riemann hypothesis. -/
theorem posSemidef_thetaTailFirstMomentBezoutian_separatedRealPacket
    {x : ℕ → ℝ} (hbase : xiRayPacketBase ≤ x 0)
    (hstep : ∀ m, xiRayPacketBase ^ 2 * x m ≤ x (m + 1)) (n : ℕ) :
    (Matrix.of fun j k : Fin n =>
      thetaTailFirstMomentBezoutian ((x j : ℝ) : ℂ)
        ((starRingEnd ℂ) ((x k : ℝ) : ℂ))).PosSemidef := by
  have hK := posSemidef_criticalLogDerivKernel_separatedRealPacket hbase hstep n
  have hone := packet_le hbase hstep
  have hhalf : ∀ j : Fin n, 1 / 2 < (((x j : ℝ) : ℂ)).re := by
    intro j
    simp only [Complex.ofReal_re]
    linarith [hone (j : ℕ), xiRayPacketBase_ge]
  have hentry : ∀ j k : Fin n,
      thetaTailFirstMomentBezoutian ((x j : ℝ) : ℂ) ((starRingEnd ℂ) ((x k : ℝ) : ℂ))
        = ((xiRayLaplace (x j) : ℝ) : ℂ) * ((xiRayLaplace (x k) : ℝ) : ℂ) *
          criticalLogDerivKernel ((x j : ℝ) : ℂ) ((x k : ℝ) : ℂ) := by
    intro j k
    have h := xiCentBezoutian_eq_mul_criticalKernel (hhalf j) (hhalf k)
    unfold thetaTailFirstMomentBezoutian
    rw [h, xiCent_ofReal, xiCent_ofReal, Complex.conj_ofReal]
  have hherm : (Matrix.of fun j k : Fin n =>
      thetaTailFirstMomentBezoutian ((x j : ℝ) : ℂ)
        ((starRingEnd ℂ) ((x k : ℝ) : ℂ))).IsHermitian := by
    ext j k
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, hentry, hentry,
      criticalLogDerivKernel_ofReal_eq, criticalLogDerivKernel_ofReal_eq,
      RCLike.star_def]
    simp only [map_mul, Complex.conj_ofReal]
    rw [show ((xiRayLogDeriv (x k) + xiRayLogDeriv (x j)) / (x k + x j) : ℝ)
        = ((xiRayLogDeriv (x j) + xiRayLogDeriv (x k)) / (x j + x k) : ℝ) by
      rw [add_comm (xiRayLogDeriv (x k)), add_comm (x k)]]
    ring
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun cv => ?_)
  have hquad := hK.dotProduct_mulVec_nonneg
    (fun j : Fin n => ((xiRayLaplace (x j) : ℝ) : ℂ) * cv j)
  have hval : star cv ⬝ᵥ (Matrix.of fun j k : Fin n =>
      thetaTailFirstMomentBezoutian ((x j : ℝ) : ℂ)
        ((starRingEnd ℂ) ((x k : ℝ) : ℂ))).mulVec cv
      = star (fun j : Fin n => ((xiRayLaplace (x j) : ℝ) : ℂ) * cv j) ⬝ᵥ
          (Matrix.of fun j k : Fin n =>
            criticalLogDerivKernel ((x j : ℝ) : ℂ) ((x k : ℝ) : ℂ)).mulVec
          (fun j : Fin n => ((xiRayLaplace (x j) : ℝ) : ℂ) * cv j) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hentry]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  rw [hval]
  exact hquad

/-- Instantiation in the literal quantifier shape of the Bezoutian Riemann-hypothesis
criterion: every separated real packet, read as a node system of the cofinal Euler
half-plane, yields a positive semidefinite criterion matrix. -/
theorem posSemidef_thetaTailFirstMomentBezoutian_packet_nodes
    {x : ℕ → ℝ} (hbase : xiRayPacketBase ≤ x 0)
    (hstep : ∀ m, xiRayPacketBase ^ 2 * x m ≤ x (m + 1)) (n : ℕ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) (hw : ∀ j, (w j : ℂ) = ((x j : ℝ) : ℂ)) :
    (Matrix.of fun j k =>
      thetaTailFirstMomentBezoutian ((w j : ℂ))
        ((starRingEnd ℂ) ((w k : ℂ)))).PosSemidef := by
  have heq : (Matrix.of fun j k : Fin n =>
      thetaTailFirstMomentBezoutian ((w j : ℂ)) ((starRingEnd ℂ) ((w k : ℂ))))
      = Matrix.of fun j k : Fin n =>
        thetaTailFirstMomentBezoutian ((x j : ℝ) : ℂ)
          ((starRingEnd ℂ) ((x k : ℝ) : ℂ)) := by
    ext j k
    rw [Matrix.of_apply, Matrix.of_apply, hw j, hw k]
  rw [heq]
  exact posSemidef_thetaTailFirstMomentBezoutian_separatedRealPacket hbase hstep n

end RHTower
