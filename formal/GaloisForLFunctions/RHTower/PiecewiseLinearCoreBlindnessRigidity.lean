import GaloisForLFunctions.RHTower.CosDilationShortSupportRigidity

/-!
# Piecewise-linear cores are never blind

Let `0 < y_1, …, y_m` be distinct and `e_1, …, e_m` real with `Σ e_j = 0` and `Σ e_j y_j = 0`, and let

`f(x) = Σ_j e_j (x − y_j)_+`   (`plCore`),

the general continuous piecewise-linear function with corners at the `y_j`, supported in
`[min y, max y]`.  If the cosine–dilation kernel `Ψ_f = Cf ⋆ f` vanishes at every integer `n ≥ 2`,
then every `e_j` vanishes (`plCore_coeff_eq_zero_of_cosDilationKernel_blind`).  There is no
restriction on the support ratio `max y / min y`.

**Proof.**
* *Closed form* (`dilationAutocorr_plCore`): `A_f(r) = (r/12) Σ_{j,l} e_j e_l |y_j − y_l/r|³`.  The
  integral `∫_0^Y (t−a)_+(t−b)_+ dt` is a polynomial in `a, b, Y` plus `|a−b|³/12`
  (`integral_hinge_mul_hinge`), and the polynomial parts cancel because `Σ e_j = Σ e_j y_j = 0`.
* *Corners of the periodization.*  By Poisson periodization
  (`tsum_dilationAutocorr_abs_eq`) `P(x) = Σ_k A_f(|x+k|)` equals `Ψ_f(0) + 2Ψ_f(1) cos 2πx`.
  Near `x = 0` the term `|y_j − y_l/(k±x)|³` is analytic unless `y_l = k y_j`, in which case it
  equals `y_j³ |x|³/(k±x)³`.  Hence `12 P(x) = R(x) + |x|³ W(x)` with `R, W` analytic near `0`.
  The analytic function `12P − R − x³W` vanishes on `(0, ε)`, hence on `(−ε, ε)`. So `W = 0` on
  `(−ε, 0)`, and in particular `W(0) = 0`.
* *Arithmetic positivity.*  With `E_j = e_j y_j^{3/2}`,
  `W(0)/2 = Σ_j E_j² + Σ_{k≥2} k^{−7/2} Σ_{y_l = k y_j} E_j E_l ≥ (1 − Σ_{k≥2} k^{−3}) Σ_j E_j²`,
  and `Σ_{k≥2} k^{−3} < 1/2` (`plCornerForm_ge`).
-/

open MeasureTheory Set Real Filter Topology

namespace RHTower

noncomputable section

variable {m : ℕ}

/-- The continuous piecewise-linear core `f(x) = Σ_j e_j (x − y_j)_+`. -/
def plCore (y e : Fin m → ℝ) (x : ℝ) : ℝ := ∑ j, e j * max (x - y j) 0

theorem continuous_plCore (y e : Fin m → ℝ) : Continuous (plCore y e) := by
  unfold plCore; fun_prop

theorem plCore_eq_zero_of_le (y e : Fin m → ℝ) {x : ℝ} (hx : ∀ j, x ≤ y j) :
    plCore y e x = 0 := by
  unfold plCore
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [max_eq_right (by linarith [hx j]), mul_zero]

theorem plCore_eq_zero_of_ge (y e : Fin m → ℝ) (he0 : ∑ j, e j = 0)
    (he1 : ∑ j, e j * y j = 0) {x : ℝ} (hx : ∀ j, y j ≤ x) : plCore y e x = 0 := by
  unfold plCore
  have h : ∀ j, e j * max (x - y j) 0 = x * e j - e j * y j := fun j => by
    rw [max_eq_left (by linarith [hx j])]; ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, he0, he1, mul_zero, sub_zero]

/-- The core vanishes off `[α, β]` when all corners lie in `[α, β]`. -/
theorem plCore_supp (y e : Fin m → ℝ) (he0 : ∑ j, e j = 0) (he1 : ∑ j, e j * y j = 0)
    {α β : ℝ} (hyα : ∀ j, α ≤ y j) (hyβ : ∀ j, y j ≤ β) (x : ℝ) (hx : plCore y e x ≠ 0) :
    α ≤ x ∧ x ≤ β := by
  constructor
  · by_contra h
    exact hx (plCore_eq_zero_of_le y e fun j => by linarith [hyα j])
  · by_contra h
    exact hx (plCore_eq_zero_of_ge y e he0 he1 fun j => by linarith [hyβ j])

/-! ### The closed form of the dilation autocorrelation -/

/-- **`∫_0^Y (t − a)_+ (t − b)_+ dt`** for `0 ≤ a ≤ Y` and `b ≤ Y`. -/
theorem integral_hinge_mul_hinge {a b Y : ℝ} (ha : 0 ≤ a) (haY : a ≤ Y) (hbY : b ≤ Y) :
    ∫ t in (0 : ℝ)..Y, max (t - a) 0 * max (t - b) 0 =
      Y ^ 3 / 3 - (a + b) * Y ^ 2 / 2 + a * b * Y +
        (a ^ 3 - 3 * a ^ 2 * b - 3 * a * b ^ 2 + b ^ 3) / 12 + |a - b| ^ 3 / 12 := by
  set M := max a b with hM
  have hM0 : 0 ≤ M := le_trans ha (le_max_left _ _)
  have hMY : M ≤ Y := max_le haY hbY
  have hcont : Continuous fun t : ℝ => max (t - a) 0 * max (t - b) 0 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := M)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h1 : ∫ t in (0 : ℝ)..M, max (t - a) 0 * max (t - b) 0 = 0 := by
    rw [intervalIntegral.integral_of_le hM0]
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    have htM : t ≤ M := ht.2
    rcases le_total a b with hab | hab
    · rw [hM, max_eq_right hab] at htM
      rw [max_eq_right (by linarith : t - b ≤ 0), mul_zero]
    · rw [hM, max_eq_left hab] at htM
      rw [max_eq_right (by linarith : t - a ≤ 0), zero_mul]
  have h2 : ∫ t in M..Y, max (t - a) 0 * max (t - b) 0 =
      (Y ^ 3 / 3 - (a + b) * Y ^ 2 / 2 + a * b * Y) -
        (M ^ 3 / 3 - (a + b) * M ^ 2 / 2 + a * b * M) := by
    have hcongr : ∫ t in M..Y, max (t - a) 0 * max (t - b) 0 =
        ∫ t in M..Y, (t - a) * (t - b) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hMY] at ht
      have hta : a ≤ t := le_trans (le_max_left _ _) ht.1
      have htb : b ≤ t := le_trans (le_max_right _ _) ht.1
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    rw [hcongr]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => t ^ 3 / 3 - (a + b) * t ^ 2 / 2 + a * b * t) (fun t _ => ?_)
      ((by fun_prop : Continuous fun t : ℝ => (t - a) * (t - b)).intervalIntegrable _ _)
    have h3 := (hasDerivAt_pow 3 t).div_const 3
    have h2 := ((hasDerivAt_pow 2 t).const_mul (a + b)).div_const 2
    have h1 := (hasDerivAt_id t).const_mul (a * b)
    exact ((h3.sub h2).add h1).congr_deriv (by push_cast; ring)
  rw [h1, h2, zero_add]
  rcases le_total a b with hab | hab
  · rw [hM, max_eq_right hab, abs_of_nonpos (by linarith : a - b ≤ 0)]
    ring
  · rw [hM, max_eq_left hab, abs_of_nonneg (by linarith : 0 ≤ a - b)]
    ring

/-- The polynomial parts cancel. -/
theorem sum_hingePoly_eq_zero (y e : Fin m → ℝ) (he0 : ∑ j, e j = 0)
    (he1 : ∑ j, e j * y j = 0) (r Y : ℝ) :
    ∑ j, ∑ l, e j * e l * (Y ^ 3 / 3 - (y j + y l / r) * Y ^ 2 / 2 + y j * (y l / r) * Y +
      (y j ^ 3 - 3 * y j ^ 2 * (y l / r) - 3 * y j * (y l / r) ^ 2 + (y l / r) ^ 3) / 12) = 0 := by
  have hinner : ∀ j, ∑ l, e j * e l * (Y ^ 3 / 3 - (y j + y l / r) * Y ^ 2 / 2 +
      y j * (y l / r) * Y +
      (y j ^ 3 - 3 * y j ^ 2 * (y l / r) - 3 * y j * (y l / r) ^ 2 + (y l / r) ^ 3) / 12) =
      e j * ((Y ^ 3 / 3 - y j * Y ^ 2 / 2 + y j ^ 3 / 12) * ∑ l, e l +
        (-(Y ^ 2 / 2) + y j * Y - y j ^ 2 / 4) / r * ∑ l, e l * y l +
        (-(y j / 4)) / r ^ 2 * ∑ l, e l * y l ^ 2 + 1 / (12 * r ^ 3) * ∑ l, e l * y l ^ 3) := by
    intro j
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases eq_or_ne r 0 with hr | hr
    · subst hr; simp; ring
    · field_simp
      ring
  rw [Finset.sum_congr rfl fun j _ => hinner j]
  set S2 := ∑ l, e l * y l ^ 2
  set S3 := ∑ l, e l * y l ^ 3
  have hj : ∀ j, e j * ((Y ^ 3 / 3 - y j * Y ^ 2 / 2 + y j ^ 3 / 12) * ∑ l, e l +
      (-(Y ^ 2 / 2) + y j * Y - y j ^ 2 / 4) / r * ∑ l, e l * y l +
      (-(y j / 4)) / r ^ 2 * S2 + 1 / (12 * r ^ 3) * S3) =
      (e j * y j) * (-(1 / 4) / r ^ 2 * S2) + e j * (1 / (12 * r ^ 3) * S3) := fun j => by
    rw [he0, he1]; ring
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, he1, he0, zero_mul, zero_mul, add_zero]

/-- **The closed form** `A_f(r) = (r/12) Σ_{j,l} e_j e_l |y_j − y_l/r|³`. -/
theorem dilationAutocorr_plCore (y e : Fin m → ℝ) (hy : ∀ j, 0 < y j) {β : ℝ}
    (hyβ : ∀ j, y j ≤ β) (he0 : ∑ j, e j = 0) (he1 : ∑ j, e j * y j = 0) {r : ℝ}
    (hr : 0 < r) :
    dilationAutocorr (plCore y e) r = r / 12 * ∑ j, ∑ l, e j * e l * |y j - y l / r| ^ 3 := by
  set Y := |β| + |β| / r with hY
  have habs : 0 ≤ |β| / r := div_nonneg (abs_nonneg _) hr.le
  have hY0 : 0 ≤ Y := by positivity
  have hβY : β ≤ Y := by linarith [le_abs_self β]
  have hyY : ∀ j, y j ≤ Y := fun j => le_trans (hyβ j) hβY
  have hyrY : ∀ l, y l / r ≤ Y := fun l => by
    have : y l / r ≤ |β| / r := div_le_div_of_nonneg_right (le_trans (hyβ l) (le_abs_self β)) hr.le
    linarith [abs_nonneg β]
  -- the half-line integral is the integral over `(0, Y]`
  have h1 : dilationAutocorr (plCore y e) r =
      ∫ t in (0 : ℝ)..Y, plCore y e t * plCore y e (r * t) := by
    unfold dilationAutocorr
    rw [intervalIntegral.integral_of_le hY0]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun t ht => ?_
    have htY : Y < t := by
      by_contra h
      exact ht.2 ⟨ht.1, le_of_not_gt h⟩
    rw [plCore_eq_zero_of_ge y e he0 he1 (fun j => by linarith [hyY j]), zero_mul]
  -- the integrand as a double sum of hinge products
  have h2 : ∀ t, plCore y e t * plCore y e (r * t) =
      ∑ j, ∑ l, r * (e j * e l) * (max (t - y j) 0 * max (t - y l / r) 0) := by
    intro t
    have hr' : ∀ l, max (r * t - y l) 0 = r * max (t - y l / r) 0 := fun l => by
      rw [mul_max_of_nonneg _ _ hr.le, mul_zero, mul_sub, mul_div_cancel₀ _ hr.ne']
    unfold plCore
    simp only [hr', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hcont : ∀ j l, Continuous fun t : ℝ =>
      r * (e j * e l) * (max (t - y j) 0 * max (t - y l / r) 0) := fun j l => by fun_prop
  rw [h1, intervalIntegral.integral_congr (g := fun t =>
      ∑ j, ∑ l, r * (e j * e l) * (max (t - y j) 0 * max (t - y l / r) 0))
      (fun t _ => h2 t)]
  rw [intervalIntegral.integral_finsetSum fun j _ => (continuous_finsetSum _
    fun l _ => hcont j l).intervalIntegrable _ _]
  simp_rw [intervalIntegral.integral_finsetSum fun l _ => (hcont _ l).intervalIntegrable _ _,
    intervalIntegral.integral_const_mul]
  have hpair : ∀ j l, ∫ t in (0 : ℝ)..Y, max (t - y j) 0 * max (t - y l / r) 0 =
      (Y ^ 3 / 3 - (y j + y l / r) * Y ^ 2 / 2 + y j * (y l / r) * Y +
        (y j ^ 3 - 3 * y j ^ 2 * (y l / r) - 3 * y j * (y l / r) ^ 2 + (y l / r) ^ 3) / 12) +
        |y j - y l / r| ^ 3 / 12 := fun j l =>
    integral_hinge_mul_hinge (hy j).le (hyY j) (hyrY l)
  simp_rw [hpair]
  have hsplit : ∀ j l, r * (e j * e l) *
      ((Y ^ 3 / 3 - (y j + y l / r) * Y ^ 2 / 2 + y j * (y l / r) * Y +
        (y j ^ 3 - 3 * y j ^ 2 * (y l / r) - 3 * y j * (y l / r) ^ 2 + (y l / r) ^ 3) / 12) +
        |y j - y l / r| ^ 3 / 12) =
      r * (e j * e l * (Y ^ 3 / 3 - (y j + y l / r) * Y ^ 2 / 2 + y j * (y l / r) * Y +
        (y j ^ 3 - 3 * y j ^ 2 * (y l / r) - 3 * y j * (y l / r) ^ 2 + (y l / r) ^ 3) / 12)) +
      r / 12 * (e j * e l * |y j - y l / r| ^ 3) := fun j l => by ring
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, sum_hingePoly_eq_zero y e he0 he1 r Y,
    mul_zero, zero_add]

/-! ### The corner form and its positivity -/

/-- The corner form `Σ_{k ≤ K} Σ_{k y_j = y_l} e_j e_l y_j³ / k²`. -/
def plCornerForm (y e : Fin m → ℝ) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, ∑ j, ∑ l,
    if ((n : ℝ) + 1) * y j = y l then e j * e l * y j ^ 3 / ((n : ℝ) + 1) ^ 2 else 0

theorem sum_sum_ite_le_left {p : Fin m → Fin m → Prop} [DecidableRel p] (g : Fin m → ℝ)
    (hg : ∀ j, 0 ≤ g j) (huniq : ∀ j l l', p j l → p j l' → l = l') :
    ∑ j, ∑ l, (if p j l then g j else 0) ≤ ∑ j, g j := by
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (p j)).card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
    huniq j a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  exact mul_le_of_le_one_left (hg j) (by exact_mod_cast hcard)

theorem sum_sum_ite_le_right {p : Fin m → Fin m → Prop} [DecidableRel p] (g : Fin m → ℝ)
    (hg : ∀ j, 0 ≤ g j) (huniq : ∀ j j' l, p j l → p j' l → j = j') :
    ∑ j, ∑ l, (if p j l then g l else 0) ≤ ∑ j, g j := by
  rw [Finset.sum_comm]
  exact sum_sum_ite_le_left (p := fun l j => p j l) g hg fun l j j' h h' => huniq j j' l h h'

theorem sum_range_one_div_succ_mul_succ_succ (K : ℕ) :
    ∑ n ∈ Finset.range K, (1 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) = 1 - 1 / ((K : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

/-- **Positivity of the corner form**: `Σ_j e_j² y_j³ / K ≤ plCornerForm y e K`. -/
theorem plCornerForm_ge (y e : Fin m → ℝ) (hy : ∀ j, 0 < y j) (hinj : Function.Injective y)
    (K : ℕ) : (1 / ((K : ℝ) + 1)) * ∑ j, e j ^ 2 * y j ^ 3 ≤ plCornerForm y e (K + 1) := by
  set E := ∑ j, e j ^ 2 * y j ^ 3 with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun j _ => by have := hy j; positivity
  unfold plCornerForm
  rw [Finset.sum_range_succ']
  -- the diagonal `k = 1`
  have hdiag : ∑ j, ∑ l, (if (((0 : ℕ) : ℝ) + 1) * y j = y l then
      e j * e l * y j ^ 3 / (((0 : ℕ) : ℝ) + 1) ^ 2 else 0) = E := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ l, (if (((0 : ℕ) : ℝ) + 1) * y j = y l then
        e j * e l * y j ^ 3 / (((0 : ℕ) : ℝ) + 1) ^ 2 else 0) =
        if j = l then e j ^ 2 * y j ^ 3 else 0 := fun l => by
      by_cases h : j = l
      · subst h; rw [if_pos (by norm_num), if_pos rfl]; push_cast; ring
      · have : ¬ (((0 : ℕ) : ℝ) + 1) * y j = y l := by
          simp only [Nat.cast_zero, zero_add, one_mul]; exact fun h' => h (hinj h')
        rw [if_neg this, if_neg h]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hdiag]
  -- each `k ≥ 2` block is at least `−(1/(2k³) + 1/(2k⁴)) E`
  have hblock : ∀ n ∈ Finset.range K,
      -(1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) * E ≤ ∑ j, ∑ l,
        (if (((n + 1 : ℕ) : ℝ) + 1) * y j = y l then
          e j * e l * y j ^ 3 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 else 0) := by
    intro n _
    set k : ℝ := ((n + 1 : ℕ) : ℝ) + 1 with hk
    have hk2 : 2 ≤ k := by simp only [hk]; push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hk0 : 0 < k := by linarith
    have hterm : ∀ j l, -(if k * y j = y l then e j ^ 2 * y j ^ 3 / (2 * k ^ 3) else 0) -
        (if k * y j = y l then e l ^ 2 * y l ^ 3 / (2 * k ^ 4) else 0) ≤
        (if k * y j = y l then e j * e l * y j ^ 3 / k ^ 2 else 0) := by
      intro j l
      by_cases h : k * y j = y l
      · simp only [if_pos h]
        rw [← h]
        have hyj := hy j
        have hy3 : 0 < y j ^ 3 := by positivity
        have hamgm : -(e j ^ 2 / k + k * e l ^ 2) ≤ 2 * (e j * e l) := by
          have : 0 ≤ (e j / Real.sqrt k + Real.sqrt k * e l) ^ 2 := sq_nonneg _
          have hs : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk0.le
          have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
          have e1 : (e j / Real.sqrt k + Real.sqrt k * e l) ^ 2 =
              e j ^ 2 / k + k * e l ^ 2 + 2 * (e j * e l) := by
            field_simp; rw [hs]; ring
          linarith
        have key : -(e j ^ 2 * y j ^ 3 / (2 * k ^ 3)) - e l ^ 2 * (k * y j) ^ 3 / (2 * k ^ 4) =
            -(e j ^ 2 / k + k * e l ^ 2) * y j ^ 3 / (2 * k ^ 2) := by
          field_simp; ring
        rw [key]
        have : -(e j ^ 2 / k + k * e l ^ 2) * y j ^ 3 / (2 * k ^ 2) ≤
            2 * (e j * e l) * y j ^ 3 / (2 * k ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hamgm hy3.le
        calc _ ≤ 2 * (e j * e l) * y j ^ 3 / (2 * k ^ 2) := this
          _ = e j * e l * y j ^ 3 / k ^ 2 := by field_simp
      · simp [if_neg h]
    have hL := sum_sum_ite_le_left (p := fun j l => k * y j = y l)
      (fun j => e j ^ 2 * y j ^ 3 / (2 * k ^ 3)) (fun j => by have := hy j; positivity)
      fun j l l' h h' => hinj (h.symm.trans h')
    have hR := sum_sum_ite_le_right (p := fun j l => k * y j = y l)
      (fun l => e l ^ 2 * y l ^ 3 / (2 * k ^ 4)) (fun j => by have := hy j; positivity)
      fun j j' l h h' => hinj (mul_left_cancel₀ hk0.ne' (h.trans h'.symm))
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hterm j l
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsum
    have hEk : ∑ j, e j ^ 2 * y j ^ 3 / (2 * k ^ 3) + ∑ j, e j ^ 2 * y j ^ 3 / (2 * k ^ 4) ≤
        1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) * E := by
      rw [← Finset.sum_div, ← Finset.sum_div, ← hE]
      have hkn : k = (n : ℝ) + 2 := by simp only [hk]; push_cast; ring
      rw [hkn]
      have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
      have hineq : 1 / (2 * ((n : ℝ) + 2) ^ 3) + 1 / (2 * ((n : ℝ) + 2) ^ 4) ≤
          1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith [pow_pos (show (0 : ℝ) < n + 2 by linarith) 3,
          pow_pos (show (0 : ℝ) < n + 2 by linarith) 4,
          pow_pos (show (0 : ℝ) < n + 2 by linarith) 5,
          pow_pos (show (0 : ℝ) < n + 2 by linarith) 6, mul_nonneg hn0 hn0]
      calc E / (2 * ((n : ℝ) + 2) ^ 3) + E / (2 * ((n : ℝ) + 2) ^ 4) =
            (1 / (2 * ((n : ℝ) + 2) ^ 3) + 1 / (2 * ((n : ℝ) + 2) ^ 4)) * E := by ring
        _ ≤ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) * E := mul_le_mul_of_nonneg_right hineq hE0
    linarith
  have htot := Finset.sum_le_sum hblock
  rw [← Finset.sum_mul, Finset.sum_neg_distrib, sum_range_one_div_succ_mul_succ_succ] at htot
  have : (1 / ((K : ℝ) + 1)) * E = E + -(1 - 1 / ((K : ℝ) + 1)) * E := by ring
  rw [this]
  linarith

/-! ### Corners of the periodization -/

/-- `12 A_f(t) = Σ_{j,l} e_j e_l |t y_j − y_l|³ / t²` for `t > 0`. -/
theorem twelve_mul_dilationAutocorr_plCore (y e : Fin m → ℝ) (hy : ∀ j, 0 < y j) {β : ℝ}
    (hyβ : ∀ j, y j ≤ β) (he0 : ∑ j, e j = 0) (he1 : ∑ j, e j * y j = 0) {t : ℝ}
    (ht : 0 < t) :
    12 * dilationAutocorr (plCore y e) t =
      ∑ j, ∑ l, e j * e l * (|t * y j - y l| ^ 3 / t ^ 2) := by
  rw [dilationAutocorr_plCore y e hy hyβ he0 he1 ht, ← mul_assoc,
    show 12 * (t / 12) = t by ring, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : y j - y l / t = (t * y j - y l) / t := by field_simp
  rw [h, abs_div, abs_of_pos ht, div_pow]
  field_simp

/-- The corner coefficient of `(k, j, l)`: `e_j e_l y_j³` if `k y_j = y_l`. -/
def plKinkCoeff (y e : Fin m → ℝ) (k : ℝ) (j l : Fin m) : ℝ :=
  if k * y j = y l then e j * e l * y j ^ 3 else 0

/-- The smooth coefficient of `(k, j, l)`: `±e_j e_l` off the corners. -/
def plSmoothCoeff (y e : Fin m → ℝ) (k : ℝ) (j l : Fin m) : ℝ :=
  if k * y j = y l then 0 else e j * e l * (if 0 < k * y j - y l then 1 else -1)

/-- `((k+x)a − b)³/(k+x)² + ((k−x)a − b)³/(k−x)²`. -/
def plCube (a b k x : ℝ) : ℝ := ((k + x) * a - b) ^ 3 / (k + x) ^ 2 + ((k - x) * a - b) ^ 3 / (k - x) ^ 2

/-- `1/(k+x)² + 1/(k−x)²`. -/
def plInvSq (k x : ℝ) : ℝ := 1 / (k + x) ^ 2 + 1 / (k - x) ^ 2

/-- The smooth part of `12 Σ_{k ≤ N} (A_f(k+x) + A_f(k−x))`. -/
def plSmooth (y e : Fin m → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ j, ∑ l, plSmoothCoeff y e ((n : ℝ) + 1) j l * plCube (y j) (y l) ((n : ℝ) + 1) x

/-- The corner part: the coefficient of `|x|³`. -/
def plKink (y e : Fin m → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ j, ∑ l, plKinkCoeff y e ((n : ℝ) + 1) j l * plInvSq ((n : ℝ) + 1) x

/-- One corner term near `x = 0`. -/
theorem eventually_plTerm (y e : Fin m → ℝ) (hy : ∀ j, 0 < y j) (k : ℝ) (j l : Fin m) :
    ∀ᶠ x in 𝓝 (0 : ℝ), e j * e l * (|(k + x) * y j - y l| ^ 3 / (k + x) ^ 2 +
      |(k - x) * y j - y l| ^ 3 / (k - x) ^ 2) =
      plSmoothCoeff y e k j l * plCube (y j) (y l) k x +
        |x| ^ 3 * (plKinkCoeff y e k j l * plInvSq k x) := by
  unfold plSmoothCoeff plKinkCoeff plCube plInvSq
  by_cases hkink : k * y j = y l
  · refine Eventually.of_forall fun x => ?_
    rw [if_pos hkink, if_pos hkink]
    have h1 : (k + x) * y j - y l = x * y j := by rw [← hkink]; ring
    have h2 : (k - x) * y j - y l = -(x * y j) := by rw [← hkink]; ring
    rw [h1, h2, abs_neg, abs_mul, abs_of_pos (hy j), mul_pow]
    ring
  · rw [if_neg hkink, if_neg hkink]
    have hc1 : ContinuousAt (fun x : ℝ => (k + x) * y j - y l) 0 := by fun_prop
    have hc2 : ContinuousAt (fun x : ℝ => (k - x) * y j - y l) 0 := by fun_prop
    by_cases hpos : 0 < k * y j - y l
    · have h0 : 0 < (k + 0) * y j - y l := by simpa using hpos
      have h0' : 0 < (k - 0) * y j - y l := by simpa using hpos
      filter_upwards [hc1.eventually (lt_mem_nhds h0), hc2.eventually (lt_mem_nhds h0')]
        with x hx1 hx2
      rw [if_pos hpos, abs_of_pos hx1, abs_of_pos hx2]
      ring
    · have hneg : k * y j - y l < 0 := lt_of_le_of_ne (not_lt.mp hpos)
        (fun h => hkink (by linarith))
      have h0 : (k + 0) * y j - y l < 0 := by simpa using hneg
      have h0' : (k - 0) * y j - y l < 0 := by simpa using hneg
      filter_upwards [hc1.eventually (gt_mem_nhds h0), hc2.eventually (gt_mem_nhds h0')]
        with x hx1 hx2
      rw [if_neg hpos, abs_of_neg hx1, abs_of_neg hx2]
      ring

/-- The cube term is analytic for `|x| < 1/2`, `k ≥ 1`. -/
theorem analyticAt_plCube (a b : ℝ) {k x : ℝ} (hk : 1 ≤ k) (hx : |x| < 1 / 2) :
    AnalyticAt ℝ (plCube a b k) x := by
  have h1 : (k + x) ^ 2 ≠ 0 := pow_ne_zero _ (by linarith [abs_lt.mp hx])
  have h2 : (k - x) ^ 2 ≠ 0 := pow_ne_zero _ (by linarith [abs_lt.mp hx])
  unfold plCube
  fun_prop (disch := assumption)

theorem analyticAt_plInvSq {k x : ℝ} (hk : 1 ≤ k) (hx : |x| < 1 / 2) :
    AnalyticAt ℝ (plInvSq k) x := by
  have h1 : (k + x) ^ 2 ≠ 0 := pow_ne_zero _ (by linarith [abs_lt.mp hx])
  have h2 : (k - x) ^ 2 ≠ 0 := pow_ne_zero _ (by linarith [abs_lt.mp hx])
  unfold plInvSq
  fun_prop (disch := assumption)

theorem one_le_natCast_add_one (n : ℕ) : (1 : ℝ) ≤ (n : ℝ) + 1 := by
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

theorem analyticAt_fun_finsetSum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ} {x : ℝ}
    (h : ∀ i ∈ s, AnalyticAt ℝ (F i) x) : AnalyticAt ℝ (fun t => ∑ i ∈ s, F i t) x := by
  have := Finset.analyticAt_sum s h
  convert this using 1
  funext t
  simp only [Finset.sum_apply]

theorem analyticAt_plSmooth (y e : Fin m → ℝ) (N : ℕ) {x : ℝ} (hx : |x| < 1 / 2) :
    AnalyticAt ℝ (plSmooth y e N) x := by
  unfold plSmooth
  refine analyticAt_fun_finsetSum _ fun n _ => analyticAt_fun_finsetSum _ fun j _ =>
    analyticAt_fun_finsetSum _ fun l _ => ?_
  exact analyticAt_const.mul (analyticAt_plCube _ _ (one_le_natCast_add_one n) hx)

theorem analyticAt_plKink (y e : Fin m → ℝ) (N : ℕ) {x : ℝ} (hx : |x| < 1 / 2) :
    AnalyticAt ℝ (plKink y e N) x := by
  unfold plKink
  refine analyticAt_fun_finsetSum _ fun n _ => analyticAt_fun_finsetSum _ fun j _ =>
    analyticAt_fun_finsetSum _ fun l _ => ?_
  exact analyticAt_const.mul (analyticAt_plInvSq (one_le_natCast_add_one n) hx)

/-- At the origin the corner part is twice the corner form. -/
theorem plKink_zero (y e : Fin m → ℝ) (N : ℕ) : plKink y e N 0 = 2 * plCornerForm y e N := by
  unfold plKink plCornerForm plKinkCoeff plInvSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · have : (n : ℝ) + 1 ≠ 0 := by linarith [one_le_natCast_add_one n]
    field_simp
    ring
  · simp

/-! ### The rigidity theorem -/

/-- **Piecewise-linear cores are never blind.**  If `0 < y_j` are distinct, `Σ e_j = 0`,
`Σ e_j y_j = 0`, and the cosine–dilation kernel of `f = Σ_j e_j (· − y_j)_+` vanishes at every
integer `n ≥ 2`, then every `e_j` vanishes. -/
theorem plCore_coeff_eq_zero_of_cosDilationKernel_blind (y e : Fin m → ℝ) (hy : ∀ j, 0 < y j)
    (hinj : Function.Injective y) (he0 : ∑ j, e j = 0) (he1 : ∑ j, e j * y j = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel (plCore y e) n = 0) (j : Fin m) :
    e j = 0 := by
  set f := plCore y e with hfdef
  set A := dilationAutocorr f with hA
  -- an interval `[α, β] ⊂ (0, ∞)` containing all corners
  set S := ∑ i, 1 / y i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hy i)).le
  set α : ℝ := 1 / (1 + S) with hαdef
  set β : ℝ := 1 + ∑ i, y i with hβdef
  have hα : 0 < α := by positivity
  have hα1 : α ≤ 1 := by rw [hαdef, div_le_one (by positivity)]; linarith
  have hyα : ∀ i, α ≤ y i := fun i => by
    rw [hαdef, div_le_iff₀ (by positivity)]
    have h1 : 1 / y i ≤ S := Finset.single_le_sum (f := fun i => 1 / y i)
      (fun i _ => (one_div_pos.mpr (hy i)).le) (Finset.mem_univ i)
    have h2 : y i * (1 / y i) = 1 := mul_one_div_cancel (hy i).ne'
    nlinarith [hy i]
  have hyβ : ∀ i, y i ≤ β := fun i => by
    have := Finset.single_le_sum (f := y) (fun i _ => (hy i).le) (Finset.mem_univ i)
    linarith
  have hαβ : α ≤ β := by
    have : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => (hy i).le
    linarith
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hsupp := plCore_supp y e he0 he1 hyα hyβ
  have hcont := continuous_plCore y e
  have hblindℤ := cosDilationKernel_int_eq_zero hcont hα hαβ hsupp hblind
  set K : ℕ := ⌈β / α⌉₊ with hK
  set N : ℕ := K + 1 with hN
  have hKge : β / α ≤ K := Nat.le_ceil _
  have hA0 : ∀ t, t ∉ Icc (α / β) (β / α) → A t = 0 := fun t ht =>
    dilationAutocorr_eq_zero_of_not_mem hα hαβ hsupp ht
  set δ₀ : ℝ := min (1 / 2) (α / β) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (by norm_num) (div_pos hα hβ0)
  -- the periodization near `0` is a finite sum
  have hper : ∀ x, |x| < δ₀ →
      ∑ n ∈ Finset.range N, (A ((n : ℝ) + 1 + x) + A ((n : ℝ) + 1 - x)) =
        cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) := by
    intro x hx
    have hx12 : |x| < 1 / 2 := lt_of_lt_of_le hx (min_le_left _ _)
    have hxab : |x| < α / β := lt_of_lt_of_le hx (min_le_right _ _)
    have hxl := abs_lt.mp hx12
    have h := tsum_dilationAutocorr_abs_eq hcont hα hαβ hsupp hblindℤ x
    set g : ℤ → ℂ := fun k => ((A |x + k| : ℝ) : ℂ) with hg
    have hNc : (N : ℝ) = K + 1 := by rw [hN]; push_cast; ring
    have hbig : ∀ n : ℕ, N ≤ n → A ((n : ℝ) + 1 + x) = 0 ∧ A ((n : ℝ) + 1 - x) = 0 := by
      intro n hn
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      constructor
      · exact hA0 _ fun hmem => by linarith [hmem.2]
      · exact hA0 _ fun hmem => by linarith [hmem.2]
    have hpos : ∀ n : ℕ, g ((n : ℤ) + 1) = ((A ((n : ℝ) + 1 + x) : ℝ) : ℂ) := by
      intro n
      simp only [hg]
      congr 2
      rw [abs_of_pos (by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
      push_cast; ring
    have hneg : ∀ n : ℕ, g (-((n : ℤ) + 1)) = ((A ((n : ℝ) + 1 - x) : ℝ) : ℂ) := by
      intro n
      simp only [hg]
      congr 2
      rw [abs_of_neg (by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])]
      push_cast; ring
    have hz : g 0 = 0 := by
      simp only [hg, Int.cast_zero, add_zero]
      rw [hA0 _ fun hmem => by linarith [hmem.1], Complex.ofReal_zero]
    have hv1 : ∀ n ∉ Finset.range N, g ((n : ℤ) + 1) = 0 := fun n hn => by
      rw [hpos, (hbig n (by simpa using hn)).1, Complex.ofReal_zero]
    have hv2 : ∀ n ∉ Finset.range N, g (-((n : ℤ) + 1)) = 0 := fun n hn => by
      rw [hneg, (hbig n (by simpa using hn)).2, Complex.ofReal_zero]
    rw [tsum_of_add_one_of_neg_add_one (summable_of_ne_finset_zero hv1)
      (summable_of_ne_finset_zero hv2), hz, add_zero, tsum_eq_sum hv1, tsum_eq_sum hv2] at h
    simp only [hpos, hneg] at h
    rw [← Finset.sum_add_distrib] at h
    have h' : ((∑ n ∈ Finset.range N, (A ((n : ℝ) + 1 + x) + A ((n : ℝ) + 1 - x)) : ℝ) : ℂ) =
        ((cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x) : ℝ) : ℂ) := by
      rw [← h]; push_cast; rfl
    exact Complex.ofReal_injective h'
  -- the corner decomposition near `0`
  have hdec : ∀ᶠ x in 𝓝 (0 : ℝ),
      12 * ∑ n ∈ Finset.range N, (A ((n : ℝ) + 1 + x) + A ((n : ℝ) + 1 - x)) =
        plSmooth y e N x + |x| ^ 3 * plKink y e N x := by
    have hall : ∀ᶠ x in 𝓝 (0 : ℝ), ∀ n ∈ Finset.range N, ∀ i l,
        e i * e l * (|((n : ℝ) + 1 + x) * y i - y l| ^ 3 / ((n : ℝ) + 1 + x) ^ 2 +
          |((n : ℝ) + 1 - x) * y i - y l| ^ 3 / ((n : ℝ) + 1 - x) ^ 2) =
        plSmoothCoeff y e ((n : ℝ) + 1) i l * plCube (y i) (y l) ((n : ℝ) + 1) x +
          |x| ^ 3 * (plKinkCoeff y e ((n : ℝ) + 1) i l * plInvSq ((n : ℝ) + 1) x) :=
      (eventually_all_finset _).mpr fun n _ => eventually_all.mpr fun i =>
        eventually_all.mpr fun l => eventually_plTerm y e hy _ i l
    have hsmall : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 1 / 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
      simpa [Real.dist_eq] using hx
    filter_upwards [hall, hsmall] with x hx hx12
    have hxl := abs_lt.mp hx12
    unfold plSmooth plKink
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hk1 : 0 < (n : ℝ) + 1 + x := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hk2 : 0 < (n : ℝ) + 1 - x := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    rw [mul_add, twelve_mul_dilationAutocorr_plCore y e hy hyβ he0 he1 hk1,
      twelve_mul_dilationAutocorr_plCore y e hy hyβ he0 he1 hk2, ← Finset.sum_add_distrib,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hx n hn i l]
    ring
  have hident : ∀ᶠ x in 𝓝 (0 : ℝ),
      12 * (cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x)) =
        plSmooth y e N x + |x| ^ 3 * plKink y e N x := by
    have hball : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < δ₀ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ₀pos] with x hx
      simpa [Real.dist_eq] using hx
    filter_upwards [hdec, hball] with x hx hxδ
    rw [← hper x hxδ]
    exact hx
  obtain ⟨ε, hε, hεid⟩ := Metric.eventually_nhds_iff.mp hident
  set ε' := min ε (1 / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'12 : ε' ≤ 1 / 2 := min_le_right _ _
  set F : ℝ → ℝ := fun x =>
    12 * (cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x)) -
      plSmooth y e N x - x ^ 3 * plKink y e N x with hF
  have hFan : AnalyticOnNhd ℝ F (Ioo (-ε') ε') := by
    intro x hx
    have hx12 : |x| < 1 / 2 := abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h1 := analyticAt_plSmooth y e N hx12
    have h2 := analyticAt_plKink y e N hx12
    have h3 : AnalyticAt ℝ (fun x : ℝ =>
        12 * (cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π * x))) x := by
      fun_prop
    exact (h3.sub h1).sub ((analyticAt_id.pow 3).mul h2)
  have hdist : ∀ x, |x| < ε' → dist x 0 < ε := fun x hx => by
    rw [Real.dist_eq, sub_zero]; linarith
  have hFpos : ∀ x ∈ Ioo 0 ε', F x = 0 := by
    intro x hx
    have := hεid (hdist x (by rw [abs_of_pos hx.1]; exact hx.2))
    simp only [hF]
    rw [this, abs_of_pos hx.1]
    ring
  have hFzero : EqOn F (fun _ => 0) (Ioo (-ε') ε') := by
    refine hFan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_Ioo
      (z₀ := ε' / 2) ⟨by linarith, by linarith⟩ ?_
    filter_upwards [Ioo_mem_nhds (by linarith : (0 : ℝ) < ε' / 2)
      (by linarith : ε' / 2 < ε')] with x hx
    exact hFpos x hx
  -- the corner part vanishes on `(−ε', 0)`
  have hKneg : ∀ x ∈ Ioo (-ε') 0, plKink y e N x = 0 := by
    intro x hx
    have h0 := hFzero ⟨hx.1, by linarith [hx.2]⟩
    have := hεid (hdist x (by rw [abs_of_neg hx.2]; linarith [hx.1]))
    simp only [hF] at h0
    rw [this, abs_of_neg hx.2] at h0
    have h2 : -2 * x ^ 3 * plKink y e N x = 0 := by linear_combination h0
    have hx3 : -2 * x ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hx.2.ne)
    exact (mul_eq_zero.mp h2).resolve_left hx3
  have hK0 : plKink y e N 0 = 0 := by
    have hc : ContinuousAt (plKink y e N) 0 :=
      (analyticAt_plKink y e N (by norm_num)).continuousAt
    have hlim : Tendsto (plKink y e N) (𝓝[<] 0) (𝓝 (plKink y e N 0)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[<] 0] plKink y e N := by
      filter_upwards [Ioo_mem_nhdsLT (by linarith : -ε' < 0)] with x hx
      exact (hKneg x hx).symm
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev)
  have hform : plCornerForm y e (K + 1) = 0 := by
    have := plKink_zero y e N
    rw [hK0] at this
    show plCornerForm y e N = 0
    linarith
  have hge := plCornerForm_ge y e hy hinj K
  rw [hform] at hge
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ e i ^ 2 * y i ^ 3 := fun i _ => by
    have := hy i; positivity
  have hsum0 : ∑ i, e i ^ 2 * y i ^ 3 ≤ 0 := by
    have hc : 0 < 1 / ((K : ℝ) + 1) := by positivity
    by_contra hneg
    have : 0 < 1 / ((K : ℝ) + 1) * ∑ i, e i ^ 2 * y i ^ 3 := mul_pos hc (lt_of_not_ge hneg)
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp
    (le_antisymm hsum0 (Finset.sum_nonneg hnn)) j (Finset.mem_univ j)
  have hy3 : y j ^ 3 ≠ 0 := pow_ne_zero _ (hy j).ne'
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp hterm).resolve_right hy3)

end

end RHTower
