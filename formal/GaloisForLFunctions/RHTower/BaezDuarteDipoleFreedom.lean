import GaloisForLFunctions.RHTower.BaezDuarteMobiusRigidity

/-!
# Báez-Duarte rows are free beyond a polynomial window

`BaezDuarteMobiusRigidity` pins Báez-Duarte approximants to `−μ` at every `n` with
`Σ_{d∣n}(2d+1) · dist < 1`, a prefix of length `≍ 1/dist`.  This file proves the complementary
freedom: moving the coefficient pair `(c_n, c_{n+1})` by the dipole `(ε, −ε)` changes the residual
by at most `2|ε|/√(n+1)`.

* `hasSum_bdStep_sub_sq`: `‖R(c) − R(c')‖² = Σ_{m≥1} |S_m(c) − S_m(c')|²/(m(m+1))`, the step
  form of the distance between two rows.
* `bdStepValue_dipole_sub`: the dipole changes the step values by `−ε({m/n} − {m/(n+1)})`.
* `norm_bdRowResidual_dipole_sub_le`: `‖R(c + dipole) − R(c)‖ ≤ 2|ε|/√(n+1)` for `2 ≤ n`.
  For `m < n` both fractional parts are exact, so the step change is `ε m/(n(n+1))`.  For
  `m ≥ n` it is at most `|ε|`.  Both are dominated by `4|ε|²/((m+n)(m+n+1))`, which telescopes
  to `4|ε|²/(n+1)`.

Reading.  At accuracy `δ` a coefficient can be moved by `O(1)` at every index `n ≳ 1/δ²`, while
it is pinned at every `n` with `σ(n) ≲ 1/δ`.  The forced Möbius prefix of the Báez-Duarte
criterion is polynomial in `1/δ`.  For the chronological criterion it is `Θ(log 1/δ)`
(`ChronologicalDilationDifferenceFreedom`): the Γ weight resolves only a logarithmic height
window, the weight `1/|s|²` a polynomial one.
-/

open MeasureTheory Set Filter

noncomputable section
namespace RHTower

/-- **Step form of the distance between two rows.** -/
theorem hasSum_bdStep_sub_sq (c c' : ℕ → ℂ) (N : ℕ) :
    HasSum (fun n : ℕ => ‖bdStepValue c N (n + 1) - bdStepValue c' N (n + 1)‖ ^ 2 /
        (((n:ℝ) + 1) * ((n:ℝ) + 2)))
      (‖bdRowResidual c N - bdRowResidual c' N‖ ^ 2) := by
  set v := bdRowResidual c N - bdRowResidual c' N
  set cell : ℕ → Set ℝ := fun n => Ico ((n:ℝ) + 1) ((n:ℝ) + 2)
  have hcell_meas : ∀ n, MeasurableSet (cell n) := fun n => measurableSet_Ico
  have hdisj : Pairwise (Function.onFun Disjoint cell) := by
    intro i j hij
    simp only [Function.onFun, cell]
    rw [Set.disjoint_left]
    intro x hxi hxj
    have h1 : (i:ℝ) + 1 ≤ x := hxi.1
    have h2 : x < (i:ℝ) + 2 := hxi.2
    have h3 : (j:ℝ) + 1 ≤ x := hxj.1
    have h4 : x < (j:ℝ) + 2 := hxj.2
    have hlt1 : (i:ℝ) < (j:ℝ) + 1 := by linarith
    have hlt2 : (j:ℝ) < (i:ℝ) + 1 := by linarith
    have : i = j := by
      have a1 : i < j + 1 := by exact_mod_cast hlt1
      have a2 : j < i + 1 := by exact_mod_cast hlt2
      omega
    exact hij this
  have hunion : (⋃ n, cell n) = Ici (1:ℝ) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ici, cell, Set.mem_Ico]
    constructor
    · rintro ⟨n, h1, _⟩
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro hx
      refine ⟨⌊x⌋₊ - 1, ?_, ?_⟩
      · have hf : (1:ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
        rw [Nat.cast_sub hf]
        push_cast
        linarith [Nat.floor_le (show 0 ≤ x by linarith)]
      · have hf : (1:ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
        rw [Nat.cast_sub hf]
        push_cast
        linarith [Nat.lt_floor_add_one x]
  have hint : Integrable (fun u => ‖(v : ℝ → ℂ) u‖ ^ 2) bdMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hIci : IntegrableOn (fun u => ‖(v : ℝ → ℂ) u‖ ^ 2) (Ici (1:ℝ)) volume := by
    rw [IntegrableOn, ← Measure.restrict_congr_set Ioi_ae_eq_Ici]
    exact hint
  have hsum := hasSum_integral_iUnion (f := fun u => ‖(v : ℝ → ℂ) u‖ ^ 2) hcell_meas hdisj
    (by rwa [hunion])
  rw [hunion] at hsum
  have htotal : (∫ u in Ici (1:ℝ), ‖(v : ℝ → ℂ) u‖ ^ 2) = ‖v‖ ^ 2 := by
    rw [GaloisForLFunctions.HTGeometry.Lp_two_norm_sq_eq_integral v, integral_Ici_eq_integral_Ioi]
  rw [htotal] at hsum
  suffices h : ∀ n : ℕ, (∫ x in cell n, ‖(v : ℝ → ℂ) x‖ ^ 2) =
      ‖bdStepValue c N (n + 1) - bdStepValue c' N (n + 1)‖ ^ 2 / (((n:ℝ) + 1) * ((n:ℝ) + 2)) by
    simpa only [h] using hsum
  intro n
  have hm0 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hne1 : ∀ᵐ u ∂(volume.restrict (cell n)), u ≠ 1 :=
    ae_restrict_of_ae (Measure.ae_ne volume 1)
  have hv : (v : ℝ → ℂ) =ᵐ[bdMeasure] fun u => bdRowResidualFun c N u - bdRowResidualFun c' N u := by
    filter_upwards [Lp.coeFn_sub (bdRowResidual c N) (bdRowResidual c' N),
      bdRowResidual_coeFn c N, bdRowResidual_coeFn c' N] with u h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hbd : ∀ᵐ u ∂volume, u ∈ Ioi (1:ℝ) →
      (v : ℝ → ℂ) u = bdRowResidualFun c N u - bdRowResidualFun c' N u :=
    (ae_restrict_iff' measurableSet_Ioi).mp hv
  have hae : ∀ᵐ u ∂(volume.restrict (cell n)),
      ‖(v : ℝ → ℂ) u‖ ^ 2 =
        ‖bdStepValue c N (n + 1) - bdStepValue c' N (n + 1)‖ ^ 2 * (u ^ 2)⁻¹ := by
    filter_upwards [hne1, ae_restrict_of_ae hbd, ae_restrict_mem (hcell_meas n)]
      with u hu1 hvu hmem
    simp only [cell, Set.mem_Ico] at hmem
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hgt : (1:ℝ) < u := lt_of_le_of_ne (by linarith [hmem.1]) (Ne.symm hu1)
    have hu0 : 0 < u := by linarith
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n:ℝ) + 1 := by push_cast; ring
    have hlo : ((n + 1 : ℕ) : ℝ) ≤ u := by rw [hcast]; exact hmem.1
    have hhi : u < ((n + 1 : ℕ) : ℝ) + 1 := by rw [hcast]; linarith [hmem.2]
    rw [hvu hgt, bdRowResidualFun_eq_step c N hlo hhi, bdRowResidualFun_eq_step c' N hlo hhi,
      ← sub_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
    field_simp
  rw [integral_congr_ae hae, integral_const_mul]
  simp only [cell]
  rw [show (n:ℝ) + 2 = ((n:ℝ) + 1) + 1 by ring, integral_Ico_inv_sq hm0]
  field_simp

/-- The dipole `ε e_n − ε e_{n+1}`. -/
def bdDipole (n : ℕ) (ε : ℂ) : ℕ → ℂ := fun k =>
  if k = n then ε else if k = n + 1 then -ε else 0

theorem bdStepValue_dipole_sub (c : ℕ → ℂ) {N n : ℕ} (hn : 1 ≤ n) (hnN : n + 1 ≤ N) (ε : ℂ)
    (m : ℕ) :
    bdStepValue (c + bdDipole n ε) N m - bdStepValue c N m =
      -(ε * (((Int.fract ((m:ℝ) / n) - Int.fract ((m:ℝ) / ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ))) := by
  unfold bdStepValue
  have hsplit : ∀ k ∈ Finset.Ioc 0 N, (c + bdDipole n ε) k * ((Int.fract ((m:ℝ) / k) : ℝ) : ℂ) =
      c k * ((Int.fract ((m:ℝ) / k) : ℝ) : ℂ) +
        bdDipole n ε k * ((Int.fract ((m:ℝ) / k) : ℝ) : ℂ) := by
    intro k _; rw [Pi.add_apply, add_mul]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hn' : n ∈ Finset.Ioc 0 N := Finset.mem_Ioc.mpr ⟨hn, by omega⟩
  have hn1 : n + 1 ∈ Finset.Ioc 0 N := Finset.mem_Ioc.mpr ⟨by omega, hnN⟩
  have hdip : ∑ k ∈ Finset.Ioc 0 N, bdDipole n ε k * ((Int.fract ((m:ℝ) / k) : ℝ) : ℂ) =
      ε * ((Int.fract ((m:ℝ) / n) : ℝ) : ℂ) -
        ε * ((Int.fract ((m:ℝ) / ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
    rw [← Finset.add_sum_erase _ _ hn', ← Finset.add_sum_erase _ _
      (Finset.mem_erase.mpr ⟨by omega, hn1⟩)]
    have hrest : ∑ k ∈ ((Finset.Ioc 0 N).erase n).erase (n + 1),
        bdDipole n ε k * ((Int.fract ((m:ℝ) / k) : ℝ) : ℂ) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk1 : k ≠ n + 1 := (Finset.mem_erase.mp hk).1
      have hk2 : k ≠ n := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      simp [bdDipole, hk1, hk2]
    rw [hrest]
    simp only [bdDipole, if_neg (by omega : n + 1 ≠ n)]
    push_cast
    ring
  rw [hdip]
  push_cast
  ring

/-- `Σ_{j<J} 1/((j+a)(j+a+1)) = 1/a − 1/(J+a)`. -/
private theorem sum_range_inv_mul_succ (a : ℝ) (ha : 0 < a) (J : ℕ) :
    ∑ j ∈ Finset.range J, 1 / (((j:ℝ) + a) * ((j:ℝ) + a + 1)) = 1 / a - 1 / ((J:ℝ) + a) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (0:ℝ) < (J:ℝ) + a := by positivity
    push_cast
    field_simp
    ring

/-- The dipole step change is dominated by the telescoping weight. -/
private theorem dipole_term_le {n : ℕ} (hn : 2 ≤ n) (j : ℕ) :
    (Int.fract (((j + 1 : ℕ) : ℝ) / n) - Int.fract (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) ^ 2 /
        (((j:ℝ) + 1) * ((j:ℝ) + 2)) ≤
      4 * (1 / (((j:ℝ) + ((n:ℝ) + 1)) * ((j:ℝ) + ((n:ℝ) + 1) + 1))) := by
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  set d := Int.fract (((j + 1 : ℕ) : ℝ) / n) - Int.fract (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
  have hpos1 : (0:ℝ) < ((j:ℝ) + 1) * ((j:ℝ) + 2) := by positivity
  have hpos2 : (0:ℝ) < ((j:ℝ) + ((n:ℝ) + 1)) * ((j:ℝ) + ((n:ℝ) + 1) + 1) := by positivity
  rw [div_le_iff₀ hpos1, mul_one_div, mul_comm, ← mul_div_assoc, le_div_iff₀ hpos2]
  rcases lt_or_ge (j + 1) n with hlt | hge
  · -- both fractional parts are exact
    have hlt' : ((j + 1 : ℕ) : ℝ) < n := by exact_mod_cast hlt
    have hfr1 : Int.fract (((j + 1 : ℕ) : ℝ) / n) = ((j + 1 : ℕ) : ℝ) / n := by
      rw [Int.fract_eq_self]; constructor
      · positivity
      · rw [div_lt_one (by linarith)]; exact hlt'
    have hfr2 : Int.fract (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) =
        ((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
      rw [Int.fract_eq_self]; constructor
      · positivity
      · rw [div_lt_one (by positivity)]; push_cast; push_cast at hlt'; linarith
    have hd : d = ((j:ℝ) + 1) / ((n:ℝ) * ((n:ℝ) + 1)) := by
      simp only [d, hfr1, hfr2]; push_cast; field_simp; ring
    rw [hd]
    have hj2 : (j:ℝ) + 2 ≤ n := by
      have : j + 2 ≤ n := by omega
      exact_mod_cast this
    have hnn : (0:ℝ) < (n:ℝ) * ((n:ℝ) + 1) := by positivity
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    set A : ℝ := (j:ℝ) + 1 with hA
    have hA0 : 0 < A := by positivity
    have hAn : A ≤ n := by linarith
    have hn0 : (0:ℝ) < n := by linarith
    have h1 : ((j:ℝ) + ((n:ℝ) + 1)) * ((j:ℝ) + ((n:ℝ) + 1) + 1) ≤ (2 * n) * (2 * n) := by
      have e1 : (j:ℝ) + ((n:ℝ) + 1) ≤ 2 * n := by linarith
      have e2 : (j:ℝ) + ((n:ℝ) + 1) + 1 ≤ 2 * n := by linarith
      exact mul_le_mul e1 e2 (by positivity) (by positivity)
    have h2 : A ^ 2 * ((2 * n) * (2 * n)) ≤ 4 * A * n ^ 3 := by
      have hAA : A * A ≤ A * n := mul_le_mul_of_nonneg_left hAn hA0.le
      have hn2' : (0:ℝ) ≤ 4 * (n:ℝ) ^ 2 := by positivity
      calc A ^ 2 * ((2 * n) * (2 * n)) = 4 * (n:ℝ) ^ 2 * (A * A) := by ring
        _ ≤ 4 * (n:ℝ) ^ 2 * (A * n) := mul_le_mul_of_nonneg_left hAA hn2'
        _ = 4 * A * n ^ 3 := by ring
    have h3 : 4 * A * n ^ 3 ≤ A * ((j:ℝ) + 2) * 4 * ((n:ℝ) * ((n:ℝ) + 1)) ^ 2 := by
      have hj2' : (1:ℝ) ≤ (j:ℝ) + 2 := by linarith
      have hn3 : (n:ℝ) ^ 3 ≤ ((j:ℝ) + 2) * ((n:ℝ) * ((n:ℝ) + 1)) ^ 2 := by
        have : (n:ℝ) ^ 3 ≤ ((n:ℝ) * ((n:ℝ) + 1)) ^ 2 := by nlinarith [hn0]
        nlinarith [this, hj2', sq_nonneg ((n:ℝ) * ((n:ℝ) + 1))]
      nlinarith [hn3, hA0]
    calc A ^ 2 * (((j:ℝ) + ((n:ℝ) + 1)) * ((j:ℝ) + ((n:ℝ) + 1) + 1))
        ≤ A ^ 2 * ((2 * n) * (2 * n)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 4 * A * n ^ 3 := h2
      _ ≤ A * ((j:ℝ) + 2) * 4 * ((n:ℝ) * ((n:ℝ) + 1)) ^ 2 := h3
  · -- both fractional parts lie in `[0,1)`
    have hge' : (n:ℝ) ≤ (j:ℝ) + 1 := by exact_mod_cast hge
    have hd1 : |d| ≤ 1 := by
      have a1 := Int.fract_nonneg (((j + 1 : ℕ) : ℝ) / n)
      have a2 := Int.fract_lt_one (((j + 1 : ℕ) : ℝ) / n)
      have a3 := Int.fract_nonneg (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      have a4 := Int.fract_lt_one (((j + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      rw [abs_le]; constructor <;> linarith
    have hd2 : d ^ 2 ≤ 1 := by
      have := sq_abs d ▸ pow_le_one₀ (abs_nonneg d) hd1
      linarith
    nlinarith [hd2, sq_nonneg d, hge', hj0]

/-- **Dipole freedom of Báez-Duarte rows.** For `2 ≤ n ≤ N − 1`, adding `ε e_n − ε e_{n+1}`
changes the residual by at most `2|ε|/√(n+1)`. -/
theorem norm_bdRowResidual_dipole_sub_le (c : ℕ → ℂ) {N n : ℕ} (hn : 2 ≤ n) (hnN : n + 1 ≤ N)
    (ε : ℂ) :
    ‖bdRowResidual (c + bdDipole n ε) N - bdRowResidual c N‖ ≤
      2 * ‖ε‖ / Real.sqrt ((n:ℝ) + 1) := by
  have hs := hasSum_bdStep_sub_sq (c + bdDipole n ε) c N
  set a : ℕ → ℝ := fun j => ‖bdStepValue (c + bdDipole n ε) N (j + 1) - bdStepValue c N (j + 1)‖ ^ 2 /
    (((j:ℝ) + 1) * ((j:ℝ) + 2)) with ha
  have hn1 : 1 ≤ n := by omega
  have hterm : ∀ j, a j ≤ ‖ε‖ ^ 2 * (4 * (1 / (((j:ℝ) + ((n:ℝ) + 1)) *
      ((j:ℝ) + ((n:ℝ) + 1) + 1)))) := by
    intro j
    simp only [ha]
    rw [bdStepValue_dipole_sub c hn1 hnN ε (j + 1), norm_neg, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (dipole_term_le hn j) (sq_nonneg _)
  have ha0 : ∀ j, 0 ≤ a j := fun j => by simp only [ha]; positivity
  have hpartial : ∀ J, ∑ j ∈ Finset.range J, a j ≤ 4 * ‖ε‖ ^ 2 / ((n:ℝ) + 1) := by
    intro J
    calc ∑ j ∈ Finset.range J, a j
        ≤ ∑ j ∈ Finset.range J, ‖ε‖ ^ 2 * (4 * (1 / (((j:ℝ) + ((n:ℝ) + 1)) *
            ((j:ℝ) + ((n:ℝ) + 1) + 1)))) := Finset.sum_le_sum fun j _ => hterm j
      _ = 4 * ‖ε‖ ^ 2 * (1 / ((n:ℝ) + 1) - 1 / ((J:ℝ) + ((n:ℝ) + 1))) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, sum_range_inv_mul_succ _ (by positivity)]; ring
      _ ≤ 4 * ‖ε‖ ^ 2 / ((n:ℝ) + 1) := by
          have : 0 ≤ 1 / ((J:ℝ) + ((n:ℝ) + 1)) := by positivity
          rw [mul_sub, mul_one_div]; linarith [mul_nonneg (by positivity : (0:ℝ) ≤ 4 * ‖ε‖ ^ 2) this]
  have hsq : ‖bdRowResidual (c + bdDipole n ε) N - bdRowResidual c N‖ ^ 2 ≤
      4 * ‖ε‖ ^ 2 / ((n:ℝ) + 1) := by
    rw [← hs.tsum_eq]
    exact Real.tsum_le_of_sum_range_le ha0 hpartial
  have hrhs : (2 * ‖ε‖ / Real.sqrt ((n:ℝ) + 1)) ^ 2 = 4 * ‖ε‖ ^ 2 / ((n:ℝ) + 1) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [← hrhs] at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end RHTower
