import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRowOfWeilsPairingAtADegreePoint
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws

/-!
# The degree points carry Weil's archimedean diagonal

Weil's archimedean form on a packet `F` in unitary logarithmic coordinates is a Lévy–Khintchine
form, `A(0)·‖F‖² + ½∬|F(u) − F(v)|² ω(|u − v|) du dv`, with the Lévy density
`ω(x) = e^{−x/2}/(1 − e^{−2x})` (`RHTower.archLevyDensity`) and the constant `A(0) = ψ(¼) − log π`
(`EF.gammaBracket 0`). This file finds the same form on the integer degree points of the
arithmetic square, the point `n` placed at `log n` with mass `1/n`.

* **The jets are the Lévy measure** (`levyKernel_eq_archLevyDensity`): for `m ≠ n`,
  `Γ_m ·_∞ Γ_n / (mn)^{3/2} = ω(|log(m/n)|)/(mn)`.
* **Lévy–Khintchine on a comb** (`sum_mul_mul_levyKernel`): for a finite set `S` of degree points
  and coefficients `C`, with `K` the kernel above and `w(m, n) = n·K(m, n)` the rate of the jump
  `n → m`,
  `Σ_{m ≠ n} C_m C_n K(m, n) = Σ_n (C_n²/n)·Σ_{m ∈ S, m ≠ n} w(m, n) − ½ Σ_{m ≠ n} (C_m − C_n)² K(m, n)`.
* **The total jump rate** (`levyRow`, `levyRow_eq`, `tendsto_sum_erase_levyWeight`): the rates
  out of `n` are summable over all degree points, with sum `H_{2n} − 3/(4n) + L_n + T_n`; `L_n`
  and `T_n` are Riemann sums of `1/(√t(1+√t)(1+t))` over `(0, 1)` and of `1/((1+√t)(1+t))` over
  `(1, ∞)`, both of integral `½ log 2 + π/4`.
* **The diagonal** (`tendsto_levyRow_sub_log`): `Σ_{m ≠ n} w(m, n) − log(n/2π) → −A(0)`.

* **The counterterm belongs to the comb** (`levyWeight_mul_mul`,
  `not_exists_counterterm_of_two_combs`): the rates are covariant under the torus, and on the comb
  of the multiples of `g` the counterterm at `g·k` is `log(k/2π)`. No function of the degree
  point serves both combs; the defect is `log g`.

So the pairing of the jets on a comb of degree points, with the entry `−log(n/2π)` per unit mass
on the diagonal, is `−A(0)·mass − Dirichlet form` up to a null sequence times the mass: Weil's
archimedean form with its own constant and its own Lévy density. The counterterm is the logarithm
of the density of the comb in logarithmic scale, divided by `2π`: on the integer degree points
`log n − log 2π`, where `log n` is the logarithm of the gluing index of `Γ_n`. It is not invariant
under the rational torus.
-/

open Finset Filter Topology
open Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The jets are the Lévy measure -/

theorem jetKernel_comm (m n : ℕ) : jetKernel m n = jetKernel n m := by
  unfold jetKernel
  rw [abs_sub_comm, add_comm (m : ℝ)]

/-- The jets in unitary normalization: `½(1/|m − n| + 1/(m + n))/√(mn)`. -/
def levyKernel (m n : ℕ) : ℝ := jetKernel m n / Real.sqrt ((m : ℝ) * n)

theorem levyKernel_comm (m n : ℕ) : levyKernel m n = levyKernel n m := by
  unfold levyKernel
  rw [jetKernel_comm, mul_comm]

/-- The rate of the jump `n → m`: `√(n/m)·½(1/|m − n| + 1/(m + n))`. -/
def levyWeight (m n : ℕ) : ℝ := Real.sqrt ((n : ℝ) / m) * jetKernel m n

theorem levyWeight_eq_mul_levyKernel {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    levyWeight m n = n * levyKernel m n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm'
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have key : Real.sqrt n / Real.sqrt m = n / (Real.sqrt m * Real.sqrt n) := by
    rw [div_eq_div_iff hsm.ne' (mul_pos hsm hsn).ne']
    linear_combination Real.sqrt m * Real.mul_self_sqrt hn'.le
  unfold levyWeight levyKernel
  rw [Real.sqrt_div hn'.le, Real.sqrt_mul hm'.le, key]
  ring

/-- `ω(log r) = √(1/r)/(1 − r⁻²)`. -/
theorem archLevyDensity_log {r : ℝ} (hr : 0 < r) :
    _root_.RHTower.archLevyDensity (Real.log r) = Real.sqrt r⁻¹ / (1 - r⁻¹ ^ 2) := by
  have h1 : -Real.log r / 2 = Real.log (Real.sqrt r⁻¹) := by
    rw [Real.log_sqrt (by positivity), Real.log_inv]
  have h2 : -2 * Real.log r = Real.log (r⁻¹ ^ 2) := by
    rw [Real.log_pow, Real.log_inv]
    push_cast
    ring
  unfold _root_.RHTower.archLevyDensity
  rw [h1, h2, Real.exp_log (by positivity), Real.exp_log (by positivity)]

/-- **The rates are the Lévy density of Weil's archimedean form** at the displacement
`log(m/n)`, with the mass `1/m` of the degree point `m`. -/
theorem levyWeight_eq_archLevyDensity {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    levyWeight m n = _root_.RHTower.archLevyDensity |Real.log ((m : ℝ) / n)| / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have h' : (m : ℝ) < n := by exact_mod_cast h
    have hlog : |Real.log ((m : ℝ) / n)| = Real.log ((n : ℝ) / m) := by
      rw [← inv_div (n : ℝ) m, Real.log_inv, abs_neg,
        abs_of_pos (Real.log_pos ((one_lt_div hm').mpr h'))]
    -- pass to `a = √m`, `b = √n`
    obtain ⟨a, ha, hma⟩ : ∃ a : ℝ, 0 < a ∧ (m : ℝ) = a ^ 2 :=
      ⟨_, Real.sqrt_pos.mpr hm', (Real.sq_sqrt hm'.le).symm⟩
    obtain ⟨b, hb, hnb⟩ : ∃ b : ℝ, 0 < b ∧ (n : ℝ) = b ^ 2 :=
      ⟨_, Real.sqrt_pos.mpr hn', (Real.sq_sqrt hn'.le).symm⟩
    have hab : a ^ 2 < b ^ 2 := by rw [← hma, ← hnb]; exact h'
    rw [hlog, archLevyDensity_log (by positivity), inv_div, levyWeight, jetKernel,
      Real.sqrt_div hn'.le, Real.sqrt_div hm'.le, hma, hnb, Real.sqrt_sq ha.le, Real.sqrt_sq hb.le,
      abs_of_neg (by linarith), neg_sub]
    have h1 : b ^ 2 - a ^ 2 ≠ 0 := (sub_pos.mpr hab).ne'
    have h2 : 1 - (a ^ 2 / b ^ 2) ^ 2 = (b ^ 2 - a ^ 2) * (b ^ 2 + a ^ 2) / b ^ 4 := by
      field_simp
      ring
    rw [h2]
    field_simp
    ring
  · have h' : (n : ℝ) < m := by exact_mod_cast h
    have hlog : |Real.log ((m : ℝ) / n)| = Real.log ((m : ℝ) / n) :=
      abs_of_pos (Real.log_pos ((one_lt_div hn').mpr h'))
    rw [hlog, archLevyDensity_log (by positivity), inv_div, levyWeight, jetKernel,
      abs_of_pos (by linarith)]
    have h1 : (m : ℝ) - n ≠ 0 := (sub_pos.mpr h').ne'
    have h2 : 1 - ((n : ℝ) / m) ^ 2 = ((m : ℝ) - n) * (m + n) / (m : ℝ) ^ 2 := by
      field_simp
      ring
    rw [h2]
    field_simp
    ring

/-- **The jets are the Lévy measure of Weil's archimedean form** on the degree points:
`½(1/|m − n| + 1/(m + n))/√(mn) = ω(|log(m/n)|)/(mn)`. -/
theorem levyKernel_eq_archLevyDensity {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    levyKernel m n =
      _root_.RHTower.archLevyDensity |Real.log ((m : ℝ) / n)| / ((m : ℝ) * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := levyWeight_eq_archLevyDensity hm hn hmn
  rw [levyWeight_eq_mul_levyKernel hm hn] at h
  rw [← div_div, ← h]
  field_simp

/-! ### Covariance under the torus -/

theorem jetKernel_mul_mul {g : ℕ} (hg : 0 < g) (m n : ℕ) :
    jetKernel (g * m) (g * n) = jetKernel m n / g := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  unfold jetKernel
  rw [show ((g * m : ℕ) : ℝ) - ((g * n : ℕ) : ℝ) = g * ((m : ℝ) - n) by push_cast; ring,
    show ((g * m : ℕ) : ℝ) + ((g * n : ℕ) : ℝ) = g * ((m : ℝ) + n) by push_cast; ring,
    abs_mul, abs_of_pos hg']
  have e : ∀ x : ℝ, 1 / ((g : ℝ) * x) = 1 / x / g := fun x => by rw [div_div, mul_comm]
  rw [e, e]
  ring

/-- **The rates are covariant under the torus**: on the comb of the multiples of `g`, whose point
`g·m` has mass `g` times its mass in the comb of all degree points, the rate of the jump
`g·n → g·m` is the rate of `n → m`. -/
theorem levyWeight_mul_mul {g : ℕ} (hg : 0 < g) (m n : ℕ) :
    levyWeight (g * m) (g * n) = levyWeight m n / g := by
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  unfold levyWeight
  rw [jetKernel_mul_mul hg, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hg']
  ring

/-! ### Lévy–Khintchine on a comb -/

/-- **Lévy–Khintchine on a finite set of points**: the off-diagonal quadratic form of a symmetric
kernel is its row sums on the squares minus half its Dirichlet form. -/
theorem sum_mul_mul_eq_row_sub_dirichlet {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (K : ι → ι → ℝ) (hK : ∀ m n, K m n = K n m) (C : ι → ℝ) :
    ∑ n ∈ S, ∑ m ∈ S.erase n, C m * C n * K m n =
      ∑ n ∈ S, C n ^ 2 * ∑ m ∈ S.erase n, K m n -
        (∑ n ∈ S, ∑ m ∈ S.erase n, (C m - C n) ^ 2 * K m n) / 2 := by
  have hswap : ∑ n ∈ S, ∑ m ∈ S.erase n, C m ^ 2 * K m n =
      ∑ n ∈ S, C n ^ 2 * ∑ m ∈ S.erase n, K m n := by
    rw [Finset.sum_comm' (s' := fun m => S.erase m) (t' := S) (fun n m => by
      simp only [Finset.mem_erase]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨Ne.symm h2, h1⟩, h3⟩,
        fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h2, Ne.symm h1, h3⟩⟩)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hK]
  have hB : ∑ n ∈ S, ∑ m ∈ S.erase n, C n ^ 2 * K m n =
      ∑ n ∈ S, C n ^ 2 * ∑ m ∈ S.erase n, K m n :=
    Finset.sum_congr rfl fun n _ => (Finset.mul_sum _ _ _).symm
  have hsplit : (∑ n ∈ S, ∑ m ∈ S.erase n, C m * C n * K m n) * 2 =
      ∑ n ∈ S, ∑ m ∈ S.erase n, C m ^ 2 * K m n +
          ∑ n ∈ S, ∑ m ∈ S.erase n, C n ^ 2 * K m n -
        ∑ n ∈ S, ∑ m ∈ S.erase n, (C m - C n) ^ 2 * K m n := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hswap, hB] at hsplit
  linarith

/-- **Lévy–Khintchine for the jets on a comb of degree points**: the off-diagonal pairing is the
jump rates on the masses `C_n²/n` minus half the Dirichlet form of the jets. -/
theorem sum_mul_mul_levyKernel (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (C : ℕ → ℝ) :
    ∑ n ∈ S, ∑ m ∈ S.erase n, C m * C n * levyKernel m n =
      ∑ n ∈ S, C n ^ 2 / n * ∑ m ∈ S.erase n, levyWeight m n -
        (∑ n ∈ S, ∑ m ∈ S.erase n, (C m - C n) ^ 2 * levyKernel m n) / 2 := by
  rw [sum_mul_mul_eq_row_sub_dirichlet S levyKernel levyKernel_comm C]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hS n hn
  rw [Finset.sum_congr rfl fun m hm =>
    levyWeight_eq_mul_levyKernel (hS m (Finset.mem_of_mem_erase hm)) (hS n hn), ← Finset.mul_sum]
  field_simp

/-! ### Riemann sums of a decreasing function against its primitive -/

/-- Mean value bound at the right endpoint. -/
theorem mul_le_sub_of_hasDerivAt {F f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Set.Icc a b)) (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x)
    (hanti : ∀ x ∈ Set.Ioo a b, f b ≤ f x) : f b * (b - a) ≤ F b - F a := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope F f hab hF hf
  have h := hanti c hc
  rwa [hcd, le_div_iff₀ (sub_pos.mpr hab)] at h

/-- Mean value bound at the left endpoint. -/
theorem sub_le_mul_of_hasDerivAt {F f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Set.Icc a b)) (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x)
    (hanti : ∀ x ∈ Set.Ioo a b, f x ≤ f a) : F b - F a ≤ f a * (b - a) := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope F f hab hF hf
  have h := hanti c hc
  rwa [hcd, div_le_iff₀ (sub_pos.mpr hab)] at h

section RiemannSums

variable {F f : ℝ → ℝ}

theorem div_le_primitive_step (hF : ContinuousOn F (Set.Ici 0))
    (hd : ∀ x, 0 < x → HasDerivAt F (f x) x) (hanti : ∀ x y, 0 < x → x ≤ y → f y ≤ f x)
    {n a : ℝ} (hn : 0 < n) (ha : 0 ≤ a) :
    f ((a + 1) / n) / n ≤ F ((a + 1) / n) - F (a / n) := by
  have ha0 : 0 ≤ a / n := div_nonneg ha hn.le
  have hlt : a / n < (a + 1) / n := by
    have : a < a + 1 := by linarith
    gcongr
  have h := mul_le_sub_of_hasDerivAt hlt (hF.mono fun x hx => ha0.trans hx.1)
    (fun x hx => hd x (ha0.trans_lt hx.1)) (fun x hx => hanti x _ (ha0.trans_lt hx.1) hx.2.le)
  have e : (a + 1) / n - a / n = 1 / n := by ring
  rwa [e, mul_one_div] at h

theorem primitive_step_le_div (hF : ContinuousOn F (Set.Ici 0))
    (hd : ∀ x, 0 < x → HasDerivAt F (f x) x) (hanti : ∀ x y, 0 < x → x ≤ y → f y ≤ f x)
    {n a : ℝ} (hn : 0 < n) (ha : 0 < a) :
    F ((a + 1) / n) - F (a / n) ≤ f (a / n) / n := by
  have ha0 : 0 < a / n := div_pos ha hn
  have hlt : a / n < (a + 1) / n := by
    have : a < a + 1 := by linarith
    gcongr
  have h := sub_le_mul_of_hasDerivAt hlt (hF.mono fun x hx => ha0.le.trans hx.1)
    (fun x hx => hd x (ha0.trans hx.1)) (fun x hx => hanti _ x ha0 hx.1.le)
  have e : (a + 1) / n - a / n = 1 / n := by ring
  rwa [e, mul_one_div] at h

/-- A right Riemann sum of a decreasing function is at most the increment of its primitive. -/
theorem sum_div_le_primitive (hF : ContinuousOn F (Set.Ici 0))
    (hd : ∀ x, 0 < x → HasDerivAt F (f x) x) (hanti : ∀ x y, 0 < x → x ≤ y → f y ≤ f x)
    {n a₀ : ℝ} (hn : 0 < n) (h0 : 0 ≤ a₀) (K : ℕ) :
    ∑ k ∈ range K, f ((a₀ + k + 1) / n) / n ≤ F ((a₀ + K) / n) - F (a₀ / n) := by
  have hsum := Finset.sum_range_sub (fun k : ℕ => F ((a₀ + (k : ℝ)) / n)) K
  simp only [Nat.cast_zero, add_zero] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Nat.cast_add_one, ← add_assoc]
  exact div_le_primitive_step hF hd hanti hn (by positivity)

/-- A left Riemann sum of a decreasing function is at least the increment of its primitive. -/
theorem primitive_le_sum_div (hF : ContinuousOn F (Set.Ici 0))
    (hd : ∀ x, 0 < x → HasDerivAt F (f x) x) (hanti : ∀ x y, 0 < x → x ≤ y → f y ≤ f x)
    {n a₀ : ℝ} (hn : 0 < n) (h0 : 0 ≤ a₀) (K : ℕ) :
    F ((a₀ + K + 1) / n) - F ((a₀ + 1) / n) ≤ ∑ k ∈ range K, f ((a₀ + k + 1) / n) / n := by
  have hsum := Finset.sum_range_sub (fun k : ℕ => F ((a₀ + (k : ℝ) + 1) / n)) K
  simp only [Nat.cast_zero, add_zero] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Nat.cast_add_one, ← add_assoc]
  exact primitive_step_le_div hF hd hanti hn (by positivity)

end RiemannSums

/-! ### The two densities and their primitives -/

/-- The density of the rates below the degree point, in the variable `t = m/n < 1`. -/
def lowDensity (t : ℝ) : ℝ := 1 / (Real.sqrt t * (1 + Real.sqrt t) * (1 + t))

/-- The density of the rates above the degree point, in the variable `t = m/n > 1`. -/
def highDensity (t : ℝ) : ℝ := 1 / ((1 + Real.sqrt t) * (1 + t))

/-- A primitive of `lowDensity`: `log(1 + √t) − ½ log(1 + t) + arctan √t`. -/
def lowPrimitive (t : ℝ) : ℝ :=
  Real.log (1 + Real.sqrt t) - Real.log (1 + t) / 2 + Real.arctan (Real.sqrt t)

/-- A primitive of `highDensity`: `arctan √t − (log(1 + √t) − ½ log(1 + t))`. -/
def highPrimitive (t : ℝ) : ℝ :=
  Real.arctan (Real.sqrt t) - (Real.log (1 + Real.sqrt t) - Real.log (1 + t) / 2)

theorem lowDensity_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : lowDensity y ≤ lowDensity x := by
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  unfold lowDensity
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem highDensity_anti {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    highDensity y ≤ highDensity x := by
  have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  unfold highDensity
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem hasDerivAt_lowPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt lowPrimitive (lowDensity t) t := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have h1 := (hs.const_add 1).log (by positivity)
  have h2 := (((hasDerivAt_id' t).const_add 1).log (by positivity)).div_const 2
  refine ((h1.sub h2).add hs.arctan).congr_deriv ?_
  show 1 / (2 * Real.sqrt t) / (1 + Real.sqrt t) - 1 / (1 + t) / 2 +
    1 / (1 + Real.sqrt t ^ 2) * (1 / (2 * Real.sqrt t)) = lowDensity t
  unfold lowDensity
  rw [Real.sq_sqrt ht.le]
  have hts : t = Real.sqrt t ^ 2 := (Real.sq_sqrt ht.le).symm
  generalize Real.sqrt t = s at hs0 hts ⊢
  subst hts
  field_simp
  ring

theorem hasDerivAt_highPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt highPrimitive (highDensity t) t := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have h1 := (hs.const_add 1).log (by positivity)
  have h2 := (((hasDerivAt_id' t).const_add 1).log (by positivity)).div_const 2
  refine (hs.arctan.sub (h1.sub h2)).congr_deriv ?_
  show 1 / (1 + Real.sqrt t ^ 2) * (1 / (2 * Real.sqrt t)) -
    (1 / (2 * Real.sqrt t) / (1 + Real.sqrt t) - 1 / (1 + t) / 2) = highDensity t
  unfold highDensity
  rw [Real.sq_sqrt ht.le]
  have hts : t = Real.sqrt t ^ 2 := (Real.sq_sqrt ht.le).symm
  generalize Real.sqrt t = s at hs0 hts ⊢
  subst hts
  field_simp
  ring

theorem continuousOn_lowPrimitive : ContinuousOn lowPrimitive (Set.Ici 0) := by
  have hs : ContinuousOn (fun t : ℝ => Real.sqrt t) (Set.Ici 0) :=
    Real.continuous_sqrt.continuousOn
  have h1 : ContinuousOn (fun t : ℝ => Real.log (1 + Real.sqrt t)) (Set.Ici 0) :=
    (continuousOn_const.add hs).log fun x _ => by
      show (1 : ℝ) + Real.sqrt x ≠ 0
      positivity
  have h2 : ContinuousOn (fun t : ℝ => Real.log (1 + t)) (Set.Ici 0) :=
    (continuousOn_const.add continuousOn_id).log fun x hx => by
      have hx0 : (0 : ℝ) ≤ x := hx
      show (1 : ℝ) + x ≠ 0
      positivity
  exact (h1.sub (h2.div_const 2)).add (Real.continuous_arctan.comp_continuousOn hs)

theorem continuousOn_highPrimitive : ContinuousOn highPrimitive (Set.Ici 0) := by
  have hs : ContinuousOn (fun t : ℝ => Real.sqrt t) (Set.Ici 0) :=
    Real.continuous_sqrt.continuousOn
  have h1 : ContinuousOn (fun t : ℝ => Real.log (1 + Real.sqrt t)) (Set.Ici 0) :=
    (continuousOn_const.add hs).log fun x _ => by
      show (1 : ℝ) + Real.sqrt x ≠ 0
      positivity
  have h2 : ContinuousOn (fun t : ℝ => Real.log (1 + t)) (Set.Ici 0) :=
    (continuousOn_const.add continuousOn_id).log fun x hx => by
      have hx0 : (0 : ℝ) ≤ x := hx
      show (1 : ℝ) + x ≠ 0
      positivity
  exact (Real.continuous_arctan.comp_continuousOn hs).sub (h1.sub (h2.div_const 2))

theorem lowPrimitive_zero : lowPrimitive 0 = 0 := by simp [lowPrimitive]

theorem lowPrimitive_one : lowPrimitive 1 = Real.log 2 / 2 + Real.pi / 4 := by
  unfold lowPrimitive
  rw [Real.sqrt_one, Real.arctan_one, show (1 : ℝ) + 1 = 2 by norm_num]
  ring

theorem highPrimitive_one : highPrimitive 1 = Real.pi / 4 - Real.log 2 / 2 := by
  unfold highPrimitive
  rw [Real.sqrt_one, Real.arctan_one, show (1 : ℝ) + 1 = 2 by norm_num]
  ring

theorem lowDensity_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ lowDensity t := by
  unfold lowDensity
  positivity

theorem lowPrimitive_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    lowPrimitive a ≤ lowPrimitive b := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have h := mul_le_sub_of_hasDerivAt hlt (continuousOn_lowPrimitive.mono fun x hx => ha.trans hx.1)
      (fun x hx => hasDerivAt_lowPrimitive (ha.trans_lt hx.1))
      (fun x hx => lowDensity_anti (ha.trans_lt hx.1) hx.2.le)
    have h0 : 0 ≤ lowDensity b * (b - a) :=
      mul_nonneg (lowDensity_nonneg (ha.trans hab)) (sub_nonneg.mpr hab)
    linarith

/-- `0 ≤ log(1 + √t) − ½ log(1 + t) ≤ 1/√t`. -/
theorem log_one_add_sqrt_sub_bounds {t : ℝ} (ht : 0 < t) :
    0 ≤ Real.log (1 + Real.sqrt t) - Real.log (1 + t) / 2 ∧
      Real.log (1 + Real.sqrt t) - Real.log (1 + t) / 2 ≤ (Real.sqrt t)⁻¹ := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hpow : Real.log ((1 + Real.sqrt t) ^ 2) = 2 * Real.log (1 + Real.sqrt t) := by
    rw [Real.log_pow]
    norm_num
  constructor
  · have h1 : Real.log (1 + t) ≤ Real.log ((1 + Real.sqrt t) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    linarith
  · have hpos : 0 < (1 + Real.sqrt t) ^ 2 / (1 + t) := by positivity
    have hlog : Real.log ((1 + Real.sqrt t) ^ 2 / (1 + t)) =
        2 * Real.log (1 + Real.sqrt t) - Real.log (1 + t) := by
      rw [Real.log_div (by positivity) (by positivity), hpow]
    have hle := Real.log_le_sub_one_of_pos hpos
    have e : (1 + Real.sqrt t) ^ 2 / (1 + t) - 1 = 2 * Real.sqrt t / (1 + t) := by
      rw [div_sub_one (by positivity)]
      congr 1
      linear_combination hs2
    have e2 : 2 * Real.sqrt t / (1 + t) ≤ 2 * (Real.sqrt t)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : (Real.sqrt t)⁻¹ * t = Real.sqrt t := by
        calc (Real.sqrt t)⁻¹ * t = (Real.sqrt t)⁻¹ * (Real.sqrt t * Real.sqrt t) := by
              rw [Real.mul_self_sqrt ht.le]
          _ = Real.sqrt t := by rw [← mul_assoc, inv_mul_cancel₀ hs0.ne', one_mul]
      nlinarith [inv_pos.mpr hs0]
    linarith

theorem highPrimitive_le {t : ℝ} (ht : 0 ≤ t) : highPrimitive t ≤ Real.pi / 2 := by
  have harc := Real.arctan_lt_pi_div_two (Real.sqrt t)
  rcases ht.eq_or_lt with rfl | hpos
  · unfold highPrimitive
    simp only [Real.sqrt_zero, add_zero, Real.log_one, zero_div, sub_zero] at harc ⊢
    linarith
  · have h := (log_one_add_sqrt_sub_bounds hpos).1
    unfold highPrimitive
    linarith

theorem tendsto_highPrimitive_atTop : Tendsto highPrimitive atTop (𝓝 (Real.pi / 2)) := by
  have harc : Tendsto (fun t : ℝ => Real.arctan (Real.sqrt t)) atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp Real.tendsto_sqrt_atTop
  have hlam : Tendsto (fun t : ℝ => Real.log (1 + Real.sqrt t) - Real.log (1 + t) / 2) atTop
      (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (𝓝 0) :=
      Real.tendsto_sqrt_atTop.inv_tendsto_atTop
    refine squeeze_zero' ?_ ?_ hinv
    · filter_upwards [eventually_gt_atTop 0] with t ht using (log_one_add_sqrt_sub_bounds ht).1
    · filter_upwards [eventually_gt_atTop 0] with t ht using (log_one_add_sqrt_sub_bounds ht).2
  have h := harc.sub hlam
  rw [sub_zero] at h
  exact h

/-! ### The rates as Riemann sums -/

/-- Below the degree point the rate is the jet plus a Riemann term of `lowDensity`. -/
theorem levyWeight_of_lt {m n : ℕ} (hm : 0 < m) (h : m < n) :
    levyWeight m n = jetKernel m n + lowDensity ((m : ℝ) / n) / n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hm.trans h
  have h' : (m : ℝ) < n := by exact_mod_cast h
  obtain ⟨a, ha, hma⟩ : ∃ a : ℝ, 0 < a ∧ (m : ℝ) = a ^ 2 :=
    ⟨_, Real.sqrt_pos.mpr hm', (Real.sq_sqrt hm'.le).symm⟩
  obtain ⟨b, hb, hnb⟩ : ∃ b : ℝ, 0 < b ∧ (n : ℝ) = b ^ 2 :=
    ⟨_, Real.sqrt_pos.mpr hn', (Real.sq_sqrt hn'.le).symm⟩
  have hab : a ^ 2 < b ^ 2 := by rw [← hma, ← hnb]; exact h'
  rw [levyWeight, jetKernel, lowDensity, Real.sqrt_div hn'.le, Real.sqrt_div hm'.le, hma, hnb,
    Real.sqrt_sq ha.le, Real.sqrt_sq hb.le, abs_of_neg (by linarith), neg_sub]
  have h1 : b ^ 2 - a ^ 2 ≠ 0 := (sub_pos.mpr hab).ne'
  field_simp
  ring

/-- Above the degree point the rate is a telescoping term plus a Riemann term of
`highDensity`. -/
theorem levyWeight_of_gt {m n : ℕ} (hn : 0 < n) (h : n < m) :
    levyWeight m n =
      (1 / ((m : ℝ) - n) - 1 / ((m : ℝ) + n)) / 2 + highDensity ((m : ℝ) / n) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hn.trans h
  have h' : (n : ℝ) < m := by exact_mod_cast h
  obtain ⟨a, ha, hma⟩ : ∃ a : ℝ, 0 < a ∧ (m : ℝ) = a ^ 2 :=
    ⟨_, Real.sqrt_pos.mpr hm', (Real.sq_sqrt hm'.le).symm⟩
  obtain ⟨b, hb, hnb⟩ : ∃ b : ℝ, 0 < b ∧ (n : ℝ) = b ^ 2 :=
    ⟨_, Real.sqrt_pos.mpr hn', (Real.sq_sqrt hn'.le).symm⟩
  have hab : b ^ 2 < a ^ 2 := by rw [← hma, ← hnb]; exact h'
  rw [levyWeight, jetKernel, highDensity, Real.sqrt_div hn'.le, Real.sqrt_div hm'.le, hma, hnb,
    Real.sqrt_sq ha.le, Real.sqrt_sq hb.le, abs_of_pos (by linarith)]
  have h1 : a ^ 2 - b ^ 2 ≠ 0 := (sub_pos.mpr hab).ne'
  field_simp
  ring

/-- The Riemann sum below the degree point. -/
def lowSum (n : ℕ) : ℝ := ∑ m ∈ Ico 1 n, lowDensity ((m : ℝ) / n) / n

theorem lowSum_eq (n : ℕ) :
    lowSum n = ∑ k ∈ range (n - 1), lowDensity ((0 + (k : ℝ) + 1) / n) / n := by
  rw [lowSum, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ((1 + k : ℕ) : ℝ) = 0 + (k : ℝ) + 1 by push_cast; ring]

theorem lowSum_le {n : ℕ} (hn : 1 ≤ n) : lowSum n ≤ lowPrimitive 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := sum_div_le_primitive continuousOn_lowPrimitive
    (fun x hx => hasDerivAt_lowPrimitive hx) (fun x y hx hxy => lowDensity_anti hx hxy)
    hn' le_rfl (n - 1)
  rw [← lowSum_eq, zero_div, lowPrimitive_zero, sub_zero, zero_add] at h
  refine h.trans (lowPrimitive_mono (by positivity) ?_)
  rw [div_le_one hn']
  exact_mod_cast Nat.sub_le n 1

theorem le_lowSum {n : ℕ} (hn : 1 ≤ n) :
    lowPrimitive 1 - lowPrimitive (1 / n) ≤ lowSum n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := primitive_le_sum_div continuousOn_lowPrimitive
    (fun x hx => hasDerivAt_lowPrimitive hx) (fun x y hx hxy => lowDensity_anti hx hxy)
    hn' le_rfl (n - 1)
  rw [← lowSum_eq, zero_add, zero_add, Nat.cast_sub hn, Nat.cast_one, sub_add_cancel,
    div_self hn'.ne'] at h
  exact h

/-- The Riemann sum below the degree point tends to `∫_0^1 dt/(√t(1+√t)(1+t)) = ½ log 2 + π/4`. -/
theorem tendsto_lowSum : Tendsto lowSum atTop (𝓝 (Real.log 2 / 2 + Real.pi / 4)) := by
  have h0 : Tendsto (fun n : ℕ => lowPrimitive (1 / (n : ℝ))) atTop (𝓝 (lowPrimitive 0)) := by
    have hw : ContinuousWithinAt lowPrimitive (Set.Ici 0) 0 :=
      continuousOn_lowPrimitive 0 Set.self_mem_Ici
    exact hw.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_atTop_nhds_zero_nat (Eventually.of_forall fun n => by
        show (0 : ℝ) ≤ 1 / (n : ℝ)
        positivity))
  have hlow : Tendsto (fun n : ℕ => lowPrimitive 1 - lowPrimitive (1 / (n : ℝ))) atTop
      (𝓝 (Real.log 2 / 2 + Real.pi / 4)) := by
    have h := (tendsto_const_nhds (x := lowPrimitive 1) (f := (atTop : Filter ℕ))).sub h0
    rw [lowPrimitive_zero, sub_zero] at h
    rw [← lowPrimitive_one]
    exact h
  have hupp : Tendsto (fun _ : ℕ => lowPrimitive 1) atTop
      (𝓝 (Real.log 2 / 2 + Real.pi / 4)) := by
    rw [lowPrimitive_one]
    exact tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn using le_lowSum hn
  · filter_upwards [eventually_ge_atTop 1] with n hn using lowSum_le hn

/-- The Riemann terms above the degree point. -/
def highTerm (n j : ℕ) : ℝ := highDensity (((n : ℝ) + j + 1) / n) / n

/-- The Riemann sum above the degree point. -/
def highSum (n : ℕ) : ℝ := ∑' j : ℕ, highTerm n j

theorem highTerm_nonneg (n j : ℕ) : 0 ≤ highTerm n j := by
  unfold highTerm highDensity
  positivity

theorem sum_highTerm_le {n : ℕ} (hn : 1 ≤ n) (J : ℕ) :
    ∑ j ∈ range J, highTerm n j ≤ Real.pi / 2 - highPrimitive 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := sum_div_le_primitive continuousOn_highPrimitive
    (fun x hx => hasDerivAt_highPrimitive hx) (fun x y hx hxy => highDensity_anti hx.le hxy)
    hn' hn'.le J
  rw [div_self hn'.ne'] at h
  exact h.trans (sub_le_sub_right (highPrimitive_le (by positivity)) _)

theorem summable_highTerm {n : ℕ} (hn : 1 ≤ n) : Summable (highTerm n) :=
  summable_of_sum_range_le (highTerm_nonneg n) (sum_highTerm_le hn)

theorem highSum_le {n : ℕ} (hn : 1 ≤ n) : highSum n ≤ Real.pi / 2 - highPrimitive 1 :=
  Real.tsum_le_of_sum_range_le (highTerm_nonneg n) (sum_highTerm_le hn)

theorem le_highSum {n : ℕ} (hn : 1 ≤ n) :
    Real.pi / 2 - highPrimitive (1 + 1 / n) ≤ highSum n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hJ : Tendsto (fun J : ℕ => ((n : ℝ) + J + 1) / n) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_add_const_left _ (n : ℝ) tendsto_natCast_atTop_atTop)).atTop_div_const hn'
  have e : ((n : ℝ) + 1) / n = 1 + 1 / n := by field_simp
  have hlim := (tendsto_highPrimitive_atTop.comp hJ).sub_const (highPrimitive (1 + 1 / n))
  refine le_of_tendsto' hlim fun J => ?_
  have h := primitive_le_sum_div continuousOn_highPrimitive
    (fun x hx => hasDerivAt_highPrimitive hx) (fun x y hx hxy => highDensity_anti hx.le hxy)
    hn' hn'.le J
  rw [e] at h
  exact h.trans ((summable_highTerm hn).sum_le_tsum _ fun j _ => highTerm_nonneg n j)

/-- The Riemann sum above the degree point tends to `∫_1^∞ dt/((1+√t)(1+t)) = π/4 + ½ log 2`. -/
theorem tendsto_highSum : Tendsto highSum atTop (𝓝 (Real.pi / 4 + Real.log 2 / 2)) := by
  have hc : Tendsto (fun n : ℕ => highPrimitive (1 + 1 / (n : ℝ))) atTop
      (𝓝 (highPrimitive 1)) := by
    have hcont : ContinuousAt highPrimitive 1 := (hasDerivAt_highPrimitive one_pos).continuousAt
    have h1 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [add_zero] at h
    exact hcont.tendsto.comp h1
  have hval : Real.pi / 2 - highPrimitive 1 = Real.pi / 4 + Real.log 2 / 2 := by
    rw [highPrimitive_one]
    ring
  have hlow : Tendsto (fun n : ℕ => Real.pi / 2 - highPrimitive (1 + 1 / (n : ℝ))) atTop
      (𝓝 (Real.pi / 4 + Real.log 2 / 2)) := by
    rw [← hval]
    exact tendsto_const_nhds.sub hc
  have hupp : Tendsto (fun _ : ℕ => Real.pi / 2 - highPrimitive 1) atTop
      (𝓝 (Real.pi / 4 + Real.log 2 / 2)) := by
    rw [hval]
    exact tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn using le_highSum hn
  · filter_upwards [eventually_ge_atTop 1] with n hn using highSum_le hn

/-! ### The telescoping part above the degree point -/

/-- `½(1/(j + 1) − 1/(2n + j + 1))`, the term `n/(m² − n²)` at `m = n + j + 1`. -/
def teleTerm (n j : ℕ) : ℝ := (1 / ((j : ℝ) + 1) - 1 / (((2 * n : ℕ) : ℝ) + j + 1)) / 2

theorem teleTerm_nonneg (n j : ℕ) : 0 ≤ teleTerm n j := by
  unfold teleTerm
  have h : 1 / (((2 * n : ℕ) : ℝ) + j + 1) ≤ 1 / ((j : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by
      have : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith)
  linarith

theorem sum_teleTerm (n J : ℕ) :
    ∑ j ∈ range J, teleTerm n j = (harm J - (harm (2 * n + J) - harm (2 * n))) / 2 := by
  unfold teleTerm
  rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_range_inv_add]
  rfl

theorem tendsto_harm_sub_harm_add (c : ℕ) :
    Tendsto (fun J : ℕ => harm J - harm (J + c)) atTop (𝓝 0) := by
  have f1 := tendsto_harm_sub_log
  have f2 := tendsto_harm_sub_log.comp (tendsto_add_atTop_nat c)
  have g : Tendsto (fun J : ℕ => Real.log ((J + c : ℕ) : ℝ) - Real.log J) atTop (𝓝 0) := by
    have h := (Real.tendsto_log_comp_add_sub_log (c : ℝ)).comp tendsto_natCast_atTop_atTop
    refine h.congr fun J => ?_
    simp only [Function.comp_apply]
    push_cast
    rfl
  have h := (f1.sub f2).sub g
  rw [sub_self, sub_zero] at h
  refine h.congr fun J => ?_
  simp only [Function.comp_apply]
  ring

theorem hasSum_teleTerm (n : ℕ) : HasSum (teleTerm n) (harm (2 * n) / 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (teleTerm_nonneg n)]
  have h := ((tendsto_harm_sub_harm_add (2 * n)).add_const (harm (2 * n))).div_const 2
  rw [zero_add] at h
  refine h.congr fun J => ?_
  rw [sum_teleTerm, Nat.add_comm (2 * n) J]
  ring

/-! ### The total jump rate -/

theorem levyWeight_add_succ {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    levyWeight (n + j + 1) n = teleTerm n j + highTerm n j := by
  have e1 : ((n + j + 1 : ℕ) : ℝ) - n = j + 1 := by push_cast; ring
  have e2 : ((n + j + 1 : ℕ) : ℝ) + n = ((2 * n : ℕ) : ℝ) + j + 1 := by push_cast; ring
  have e3 : ((n + j + 1 : ℕ) : ℝ) = (n : ℝ) + j + 1 := by push_cast; ring
  rw [levyWeight_of_gt hn (by omega), e1, e2, e3, teleTerm, highTerm]

theorem hasSum_levyWeight_above {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun j : ℕ => levyWeight (n + j + 1) n) (harm (2 * n) / 2 + highSum n) := by
  have hfun : (fun j : ℕ => levyWeight (n + j + 1) n) = fun j => teleTerm n j + highTerm n j :=
    funext (levyWeight_add_succ hn)
  rw [hfun]
  exact (hasSum_teleTerm n).add (summable_highTerm hn).hasSum

/-- The total rate of the jumps out of the degree point `n`. -/
def levyRow (n : ℕ) : ℝ :=
  ∑ m ∈ Ico 1 n, levyWeight m n + ∑' j : ℕ, levyWeight (n + j + 1) n

theorem harm_zero : harm 0 = 0 := by simp [harm]

/-- **The total jump rate**: `H_{2n} − 3/(4n)` plus the two Riemann sums. -/
theorem levyRow_eq {n : ℕ} (hn : 1 ≤ n) :
    levyRow n = harm (2 * n) - 3 / (4 * (n : ℝ)) + lowSum n + highSum n := by
  have hlow : ∑ m ∈ Ico 1 n, levyWeight m n =
      harm (2 * n) / 2 - 3 / (4 * (n : ℝ)) + lowSum n := by
    have h := sum_jetKernel_row hn le_rfl
    rw [Finset.Ioc_self, Finset.sum_empty, add_zero, Nat.sub_self, harm_zero, zero_add,
      ← two_mul] at h
    rw [Finset.sum_congr rfl fun m hm =>
      levyWeight_of_lt (Finset.mem_Ico.mp hm).1 (Finset.mem_Ico.mp hm).2,
      Finset.sum_add_distrib, h, lowSum]
  rw [levyRow, hlow, (hasSum_levyWeight_above hn).tsum_eq]
  ring

/-- The rates out of `n` into a window `[1, M]` increase to the total rate. -/
theorem tendsto_sum_erase_levyWeight {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun M : ℕ => ∑ m ∈ (Icc 1 M).erase n, levyWeight m n) atTop (𝓝 (levyRow n)) := by
  have htail := (hasSum_levyWeight_above hn).tendsto_sum_nat.comp (tendsto_sub_atTop_nat n)
  have hlim := htail.const_add (∑ m ∈ Ico 1 n, levyWeight m n)
  have hval : levyRow n =
      ∑ m ∈ Ico 1 n, levyWeight m n + (harm (2 * n) / 2 + highSum n) := by
    rw [levyRow, (hasSum_levyWeight_above hn).tsum_eq]
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop n] with M hM
  have hsplit : (Icc 1 M).erase n = Ico 1 n ∪ Ioc n M := by
    ext k
    simp only [mem_erase, mem_Icc, mem_union, mem_Ico, mem_Ioc]
    omega
  have hdisj : Disjoint (Ico 1 n) (Ioc n M) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [mem_Ico, mem_Ioc] at hk hk'
    omega
  simp only [Function.comp_apply]
  rw [hsplit, Finset.sum_union hdisj, ← Ico_succ_succ_eq_Ioc',
    Finset.sum_Ico_eq_sum_range (fun m => levyWeight m n) (n + 1) (M + 1),
    Nat.add_sub_add_right]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [Nat.add_right_comm]

/-! ### The diagonal -/

/-- **Weil's archimedean constant is the finite part of the jets on the degree points**: the total
jump rate out of `n` minus `log(n/2π)` tends to `−A(0) = γ + π/2 + log 8π`. -/
theorem tendsto_levyRow_sub_log :
    Tendsto (fun n : ℕ => levyRow n - Real.log ((n : ℝ) / (2 * Real.pi))) atTop
      (𝓝 (-EF.gammaBracket 0)) := by
  rw [_root_.RHTower.ArchimedeanAnomaly.gammaBracket_zero_eq, neg_neg]
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      show n ≤ 2 * n
      omega) tendsto_id
  have hH := tendsto_harm_sub_log.comp h2n
  have h3 : Tendsto (fun n : ℕ => 3 / (4 * (n : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have hlim := (((hH.add_const (Real.log 2 + Real.log (2 * Real.pi))).sub h3).add
    tendsto_lowSum).add tendsto_highSum
  have hval : Real.eulerMascheroniConstant + (Real.log 2 + Real.log (2 * Real.pi)) - 0 +
      (Real.log 2 / 2 + Real.pi / 4) + (Real.pi / 4 + Real.log 2 / 2) =
      Real.eulerMascheroniConstant + Real.pi / 2 + Real.log (8 * Real.pi) := by
    have h8 : Real.log (8 * Real.pi) = 2 * Real.log 2 + Real.log (2 * Real.pi) := by
      rw [show (8 : ℝ) * Real.pi = 2 ^ 2 * (2 * Real.pi) by ring,
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
      norm_num
    rw [h8]
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply]
  rw [levyRow_eq hn, Real.log_div hn'.ne' (by positivity),
    show ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) by push_cast; ring,
    Real.log_mul (by norm_num) hn'.ne']
  ring

/-- **The counterterm belongs to the comb, not to the degree point.** No function of the degree
point is the counterterm of Weil's constant both on the comb of all degree points and on the comb
of the multiples of `g ≥ 2`. On the second comb the total rate at `g·k` is the total rate of `k`
(`levyWeight_mul_mul`), so the counterterms of the two combs at the same point differ by
`log g`. -/
theorem not_exists_counterterm_of_two_combs {g : ℕ} (hg : 2 ≤ g) :
    ¬ ∃ δ : ℕ → ℝ,
      Tendsto (fun k : ℕ => levyRow k - δ k) atTop (𝓝 (-EF.gammaBracket 0)) ∧
      Tendsto (fun k : ℕ => levyRow k - δ (g * k)) atTop (𝓝 (-EF.gammaBracket 0)) := by
  rintro ⟨δ, h1, h2⟩
  have hg0 : 0 < g := by omega
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg0
  have hgk : Tendsto (fun k : ℕ => g * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k hg0) tendsto_id
  have hrow := tendsto_levyRow_sub_log
  have hc := (hrow.sub h2).sub ((hrow.comp hgk).sub (h1.comp hgk))
  have hlim : Tendsto (fun _ : ℕ => Real.log g) atTop (𝓝 0) := by
    have hz : (-EF.gammaBracket 0 - -EF.gammaBracket 0) -
        (-EF.gammaBracket 0 - -EF.gammaBracket 0) = 0 := by ring
    rw [← hz]
    refine hc.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [Function.comp_apply]
    rw [show ((g * k : ℕ) : ℝ) / (2 * Real.pi) = g * ((k : ℝ) / (2 * Real.pi)) by
      push_cast; ring, Real.log_mul hg'.ne' (by positivity)]
    ring
  have hzero : Real.log g = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have hpos : 0 < Real.log (g : ℝ) := Real.log_pos (by exact_mod_cast hg)
  linarith

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
