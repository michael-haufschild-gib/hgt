import GaloisForLFunctions.HTGeometry.CircleQuadratureSectorWolffMeasure

/-!
# Two-base Wolff configurations with sector weights

Let `φ` be the golden ratio. There is a countable family of distinct points `z_i` with
`log(5/4) ≤ Re z_i ≤ log 10`, locally finite (finitely many with `|Im z| ≤ T`), with weights
`c_i` in the sector `|c_i| ≤ 2 Re c_i`, arguments tending to `0`, one weight equal to `1`, and
`Σ|c_i|^p < ∞` for every `p > 0`. Both moment sequences vanish for every `m ≥ 1`:
`Σ_i c_i e^{m z_i} = 0` and `Σ_i c_i e^{m φ z_i} = 0` (`exists_two_base_sector_configuration`).
The largest real part is not attained.

**Construction (two-base circle quadrature).** Stage `k` uses `N_k²` points on the product grid
`z = log R_k + i(T_k + 2π a/N_k + 2π b/(φ N_k))`, `a, b < N_k`, with `T_k = 20(k + 1)`. In base
`1` a grid point is seen as `R_k^m e^{imT_k} ω^{am} β^{bm}`; in base `φ` as
`R_k^{φm} e^{imφT_k} γ^{am} ω^{bm}`.
Here `ω = e^{2πi/N}`, `β = e^{2πi/(φN)}`, `γ = e^{2πiφ/N}`. The weights are `s + u_a + v_b`.
* The constant part `s` has all moments `1 ≤ m < N` zero in both bases, since each base contains a
  full root-of-unity factor.
* The `u`-part is invisible to base `φ` below `N`. In base `1` its moment is
  `R^m e^{imT} û(m) B(m)`, with `B(m) = Σ_b β^{bm}`. The `v`-part is the mirror image, through
  `Γ(m) = Σ_a γ^{am}`.
* Choosing `û(m) = −E¹(m)/(R^m e^{imT} B(m))` and `v̂(m) = −E²(m)/(R^{φm} e^{imφT} Γ(m))` kills both
  residuals below `N` exactly (`sum_twoWeight_mul_node1_pow`, `sum_twoWeight_mul_node2_pow`).
* The Diophantine bound `‖mφ‖ ≥ 1/(3m)` (`one_div_three_mul_le_abs_mul_gold_sub`) gives
  `|B(m)| ≥ 1/(5N)` and `|Γ(m)| ≥ 1/(10N)`, so `|u| ≤ 5NL` and `|v| ≤ 10NL`.
* The shift `s = (2^k + 3)·15 N L` puts the weights in the sector, and the radius gain of
  `CircleQuadratureAnnihilating` controls the moments `m ≥ N`.
-/

open Complex Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.TwoBaseQuadrature

open CircleQuadratureAnnihilating

noncomputable section

local notation "g" => Real.goldenRatio

/-! ## The golden ratio is badly approximable -/

theorem gold_lt_two' : g < 2 := Real.goldenRatio_lt_two

theorem one_lt_gold' : 1 < g := Real.one_lt_goldenRatio

/-- `‖mφ‖ ≥ 1/(3m)`: from `(n − mφ)(n − mψ) = n² − nm − m²`, a nonzero integer. -/
theorem one_div_three_mul_le_abs_mul_gold_sub {m : ℕ} (hm : 1 ≤ m) (n : ℤ) :
    1 / (3 * (m : ℝ)) ≤ |(m : ℝ) * g - n| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set ψ := Real.goldenConj
  have hsum : g + ψ = 1 := Real.goldenRatio_add_goldenConj
  have hprod : g * ψ = -1 := Real.goldenRatio_mul_goldenConj
  have hdiff : g - ψ = √5 := Real.goldenRatio_sub_goldenConj
  have hkey : ((n : ℝ) - m * g) * ((n : ℝ) - m * ψ) = ((n ^ 2 - n * m - m ^ 2 : ℤ) : ℝ) := by
    push_cast
    have : ((n : ℝ) - m * g) * ((n : ℝ) - m * ψ) = n ^ 2 - n * m * (g + ψ) + m ^ 2 * (g * ψ) := by
      ring
    rw [this, hsum, hprod]; ring
  have hne : (n ^ 2 - n * m - m ^ 2 : ℤ) ≠ 0 := by
    intro h0
    have h0' : ((n : ℝ) - m * g) * ((n : ℝ) - m * ψ) = 0 := by rw [hkey, h0]; simp
    rcases mul_eq_zero.mp h0' with h | h
    · apply Real.goldenRatio_irrational
      have hg : g = (n : ℝ) / m := by rw [eq_div_iff hm0.ne']; linarith
      exact ⟨(n : ℚ) / m, by push_cast; exact hg.symm⟩
    · apply Real.goldenConj_irrational
      have hg : ψ = (n : ℝ) / m := by rw [eq_div_iff hm0.ne']; linarith
      exact ⟨(n : ℚ) / m, by push_cast; exact hg.symm⟩
  have hone : (1 : ℝ) ≤ |((n ^ 2 - n * m - m ^ 2 : ℤ) : ℝ)| := by
    have := Int.one_le_abs hne
    exact_mod_cast this
  rw [← hkey, abs_mul] at hone
  by_contra hlt
  push Not at hlt
  have h5 : √5 ≤ 9 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hψ : |(n : ℝ) - m * ψ| ≤ |(m : ℝ) * g - n| + m * √5 := by
    have e : (n : ℝ) - m * ψ = -((m : ℝ) * g - n) + m * (g - ψ) := by ring
    rw [e, hdiff]
    refine (abs_add_le _ _).trans ?_
    have hpos : |(m : ℝ) * √5| = m * √5 := abs_of_nonneg (by positivity)
    rw [abs_neg, hpos]
  have habs : |(n : ℝ) - m * g| = |(m : ℝ) * g - n| := abs_sub_comm _ _
  rw [habs] at hone
  have hx0 : 0 ≤ |(m : ℝ) * g - n| := abs_nonneg _
  have h3 : |(m : ℝ) * g - n| * (3 * m) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hlt; linarith
  have hb : |(n : ℝ) - m * ψ| ≤ 1 / (3 * m) + m * (9 / 4) := by
    have : (m : ℝ) * √5 ≤ m * (9 / 4) := mul_le_mul_of_nonneg_left h5 hm0.le
    linarith
  have hprod_lt : |(m : ℝ) * g - n| * |(n : ℝ) - m * ψ| < 1 := by
    calc |(m : ℝ) * g - n| * |(n : ℝ) - m * ψ|
        ≤ |(m : ℝ) * g - n| * (1 / (3 * m) + m * (9 / 4)) :=
          mul_le_mul_of_nonneg_left hb hx0
      _ = |(m : ℝ) * g - n| * (3 * m) * (1 / (9 * m ^ 2) + 3 / 4) := by field_simp; ring
      _ ≤ 1 * (1 / (9 * m ^ 2) + 3 / 4) := by
          apply mul_le_mul_of_nonneg_right h3.le (by positivity)
      _ < 1 := by
          have : 1 / (9 * (m : ℝ) ^ 2) ≤ 1 / 9 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
          linarith
  linarith

/-- `‖m/φ‖ ≥ 1/(3m)`, since `1/φ = φ − 1`. -/
theorem one_div_three_mul_le_abs_div_gold_sub {m : ℕ} (hm : 1 ≤ m) (n : ℤ) :
    1 / (3 * (m : ℝ)) ≤ |(m : ℝ) / g - n| := by
  have hinv : 1 / g = g - 1 := by
    have h := Real.goldenRatio_sq
    rw [div_eq_iff Real.goldenRatio_ne_zero]
    linear_combination (-1 : ℝ) * h
  have e : (m : ℝ) / g - n = (m : ℝ) * g - ((n + m : ℤ) : ℝ) := by
    rw [div_eq_mul_one_div, hinv]; push_cast; ring
  rw [e]
  exact one_div_three_mul_le_abs_mul_gold_sub hm _

/-! ## Chord bounds -/

/-- `‖e^{2πix} − 1‖ ≥ 4δ` when `x` is at distance `≥ δ` from every integer. -/
theorem four_mul_le_norm_exp_sub_one {x δ : ℝ} (h : ∀ n : ℤ, δ ≤ |x - n|) :
    4 * δ ≤ ‖Complex.exp (I * ((2 * Real.pi * x : ℝ) : ℂ)) - 1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  set n := round x
  set t := x - n with ht
  have htn : |t| ≤ 1 / 2 := abs_sub_round x
  have hδ := h n
  have hsin : Real.sin (2 * Real.pi * x / 2) = (-1) ^ n * Real.sin (Real.pi * t) := by
    rw [← Real.sin_add_int_mul_pi, ht]; congr 1; ring
  rw [hsin, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hπ := Real.pi_pos
  have hj : 2 / Real.pi * (Real.pi * |t|) ≤ Real.sin (Real.pi * |t|) :=
    Real.mul_le_sin (by positivity) (by nlinarith [abs_nonneg t])
  have habs : |Real.sin (Real.pi * t)| = Real.sin (Real.pi * |t|) := by
    rcases le_or_gt 0 t with h0 | h0
    · have ht2 : t ≤ 1 / 2 := by rw [abs_of_nonneg h0] at htn; exact htn
      rw [abs_of_nonneg h0, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    · rw [abs_of_neg h0, show Real.pi * t = -(Real.pi * -t) by ring, Real.sin_neg, abs_neg,
        abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith [abs_of_neg h0])
  rw [habs]
  have : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by field_simp
  have hδt : δ ≤ |t| := hδ
  linarith

/-- `‖e^{iy} − 1‖ ≤ |y|`. -/
theorem norm_exp_I_mul_sub_one_le (y : ℝ) : ‖Complex.exp (I * (y : ℂ)) - 1‖ ≤ |y| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have := Real.abs_sin_le_abs (x := y / 2)
  rw [abs_div, abs_two] at this
  linarith

/-- A geometric sum `Σ_{b<N} q^b` with `‖q^N − 1‖ ≥ A > 0` and `‖q − 1‖ ≤ D` has modulus `≥ A/D`. -/
theorem le_norm_geom_sum {q : ℂ} {N : ℕ} {A D : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hnum : A ≤ ‖q ^ N - 1‖) (hden : ‖q - 1‖ ≤ D) : A / D ≤ ‖∑ b ∈ range N, q ^ b‖ := by
  have hq1 : q ≠ 1 := by
    intro h; rw [h, one_pow, sub_self, norm_zero] at hnum; linarith
  rw [geom_sum_eq hq1, norm_div]
  have hpos : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq1)
  rw [div_le_div_iff₀ hD hpos]
  calc A * ‖q - 1‖ ≤ ‖q ^ N - 1‖ * ‖q - 1‖ := mul_le_mul_of_nonneg_right hnum hpos.le
    _ ≤ ‖q ^ N - 1‖ * D := mul_le_mul_of_nonneg_left hden (norm_nonneg _)

/-! ## Stage data -/

/-- Heights `T_k = 20(k + 1)`. -/
def height (k : ℕ) : ℝ := 20 * ((k : ℝ) + 1)

/-- The base-`φ` radius `R_k^φ = exp(φ log R_k)`. -/
def radius2 (k : ℕ) : ℝ := Real.exp (g * Real.log (radius k))

/-- `β_k = e^{2πi/(φ N_k)}`. -/
def betaRoot (k : ℕ) : ℂ := Complex.exp (I * ((2 * Real.pi / (g * nodeCount k) : ℝ) : ℂ))

/-- `γ_k = e^{2πiφ/N_k}`. -/
def gammaRoot (k : ℕ) : ℂ := Complex.exp (I * ((2 * Real.pi * g / nodeCount k : ℝ) : ℂ))

/-- Base-`1` grid values `R_k e^{iT_k} ω^a β^b`. -/
def node1 (k a b : ℕ) : ℂ :=
  (radius k : ℂ) * Complex.exp (I * (height k : ℂ)) * root k ^ a * betaRoot k ^ b

/-- Base-`φ` grid values `R_k^φ e^{iφT_k} γ^a ω^b`. -/
def node2 (k a b : ℕ) : ℂ :=
  (radius2 k : ℂ) * Complex.exp (I * ((g * height k : ℝ) : ℂ)) * gammaRoot k ^ a * root k ^ b

/-- `B_k(m) = Σ_b β^{bm}`. -/
def charB (k m : ℕ) : ℂ := ∑ b ∈ range (nodeCount k), (betaRoot k ^ m) ^ b

/-- `Γ_k(m) = Σ_a γ^{am}`. -/
def charG (k m : ℕ) : ℂ := ∑ a ∈ range (nodeCount k), (gammaRoot k ^ m) ^ a

/-- Base-`1` transfer factor. -/
def transfer1 (k m : ℕ) : ℂ := ((radius k : ℂ) * Complex.exp (I * (height k : ℂ))) ^ m * charB k m

/-- Base-`φ` transfer factor. -/
def transfer2 (k m : ℕ) : ℂ :=
  ((radius2 k : ℂ) * Complex.exp (I * ((g * height k : ℝ) : ℂ))) ^ m * charG k m

/-- Shift multiplier `15 (2^k + 3) N_k`. -/
def twoShift (k : ℕ) : ℝ := 15 * (2 ^ k + 3) * nodeCount k

/-- Bounds `L_0 = 1`, `L_{k+1} = (1 + 15 N_k³ (2^k + 4)) L_k / 2^{a_k}`. -/
def twoBound : ℕ → ℝ
  | 0 => 1
  | k + 1 => (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k / 2 ^ gainExp k

/-- Residual moment sequences in both bases, defined together. -/
def twoResidual : ℕ → (ℕ → ℂ) × (ℕ → ℂ)
  | 0 => (fun m => (5 / 4 : ℂ) ^ m,
      fun m => ((Real.exp (g * Real.log (5 / 4)) : ℝ) : ℂ) ^ m)
  | k + 1 =>
    let E := twoResidual k
    let u : ℕ → ℂ := fun a => (1 / (nodeCount k : ℂ)) *
      ∑ i ∈ Ico 1 (nodeCount k), (-E.1 i / transfer1 k i) / root k ^ (i * a)
    let v : ℕ → ℂ := fun b => (1 / (nodeCount k : ℂ)) *
      ∑ i ∈ Ico 1 (nodeCount k), (-E.2 i / transfer2 k i) / root k ^ (i * b)
    let w : ℕ → ℕ → ℂ := fun a b => ((twoShift k * twoBound k : ℝ) : ℂ) + u a + v b
    (fun m => E.1 m + ∑ a ∈ range (nodeCount k), ∑ b ∈ range (nodeCount k),
        w a b * node1 k a b ^ m,
      fun m => E.2 m + ∑ a ∈ range (nodeCount k), ∑ b ∈ range (nodeCount k),
        w a b * node2 k a b ^ m)

/-- The base-`1` residual. -/
def res1 (k m : ℕ) : ℂ := (twoResidual k).1 m

/-- The base-`φ` residual. -/
def res2 (k m : ℕ) : ℂ := (twoResidual k).2 m

/-- The `u`-weights. -/
def uW (k a : ℕ) : ℂ :=
  (1 / (nodeCount k : ℂ)) *
    ∑ i ∈ Ico 1 (nodeCount k), (-res1 k i / transfer1 k i) / root k ^ (i * a)

/-- The `v`-weights. -/
def vW (k b : ℕ) : ℂ :=
  (1 / (nodeCount k : ℂ)) *
    ∑ i ∈ Ico 1 (nodeCount k), (-res2 k i / transfer2 k i) / root k ^ (i * b)

/-- The grid weights `s + u_a + v_b`. -/
def twoWeight (k a b : ℕ) : ℂ := ((twoShift k * twoBound k : ℝ) : ℂ) + uW k a + vW k b

theorem res1_succ (k m : ℕ) : res1 (k + 1) m = res1 k m +
    ∑ a ∈ range (nodeCount k), ∑ b ∈ range (nodeCount k), twoWeight k a b * node1 k a b ^ m :=
  rfl

theorem res2_succ (k m : ℕ) : res2 (k + 1) m = res2 k m +
    ∑ a ∈ range (nodeCount k), ∑ b ∈ range (nodeCount k), twoWeight k a b * node2 k a b ^ m :=
  rfl

/-! ## Norms -/

theorem norm_exp_I_mul (y : ℝ) : ‖Complex.exp (I * (y : ℂ))‖ = 1 := Complex.norm_exp_I_mul_ofReal y

theorem norm_betaRoot (k : ℕ) : ‖betaRoot k‖ = 1 := norm_exp_I_mul _

theorem norm_gammaRoot (k : ℕ) : ‖gammaRoot k‖ = 1 := norm_exp_I_mul _

theorem radius2_pos (k : ℕ) : 0 < radius2 k := Real.exp_pos _

theorem norm_node1 (k a b : ℕ) : ‖node1 k a b‖ = radius k := by
  unfold node1
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_root, norm_betaRoot, norm_exp_I_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (radius_pos k)]
  ring

theorem norm_node2 (k a b : ℕ) : ‖node2 k a b‖ = radius2 k := by
  unfold node2
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_root, norm_gammaRoot, norm_exp_I_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (radius2_pos k)]
  ring

theorem node1_pow (k a b m : ℕ) : node1 k a b ^ m =
    ((radius k : ℂ) * Complex.exp (I * (height k : ℂ))) ^ m *
      ((root k ^ m) ^ a * (betaRoot k ^ m) ^ b) := by
  unfold node1
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm a m, mul_comm b m]
  ring

theorem node2_pow (k a b m : ℕ) : node2 k a b ^ m =
    ((radius2 k : ℂ) * Complex.exp (I * ((g * height k : ℝ) : ℂ))) ^ m *
      ((gammaRoot k ^ m) ^ a * (root k ^ m) ^ b) := by
  unfold node2
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm a m, mul_comm b m]
  ring

/-! ## Character sums -/

theorem sum_root_pow (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    ∑ a ∈ range (nodeCount k), (root k ^ m) ^ a = 0 := by
  have hζ := isPrimitiveRoot_root k
  have hζ1 : root k ^ m ≠ 1 := by
    intro h
    have := hζ.pow_inj hm (nodeCount_pos k) (by rw [h, pow_zero])
    omega
  have hζN : (root k ^ m) ^ nodeCount k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [geom_sum_eq hζ1, hζN, sub_self, zero_div]

theorem sum_root_pow_div (k : ℕ) {m i : ℕ} (hm : m < nodeCount k) (hi : i < nodeCount k) :
    ∑ a ∈ range (nodeCount k), (root k ^ m) ^ a / root k ^ (i * a) =
      if m = i then (nodeCount k : ℂ) else 0 := by
  have hζ := isPrimitiveRoot_root k
  have hω0 : root k ≠ 0 := by
    intro h; have := norm_root k; rw [h, norm_zero] at this; norm_num at this
  have hterm : ∀ a, (root k ^ m) ^ a / root k ^ (i * a) = (root k ^ m / root k ^ i) ^ a := by
    intro a; rw [pow_mul, div_pow]
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  split_ifs with hmi
  · subst hmi
    rw [div_self (pow_ne_zero _ hω0)]
    simp
  · have hζ1 : root k ^ m / root k ^ i ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq (pow_ne_zero _ hω0)] at h
      exact hmi (hζ.pow_inj hm hi h)
    have hζN : (root k ^ m / root k ^ i) ^ nodeCount k = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm m, mul_comm i, pow_mul, pow_mul, hζ.pow_eq_one,
        one_pow, one_pow, div_one]
    rw [geom_sum_eq hζ1, hζN, sub_self, zero_div]

theorem pi_mul_three_lt_ten : 3 * Real.pi < 10 := by linarith [Real.pi_lt_d2]

/-- `|B_k(m)| ≥ 1/(5N_k)` for `1 ≤ m < N_k`. -/
theorem norm_charB_ge (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    1 / (5 * (nodeCount k : ℝ)) ≤ ‖charB k m‖ := by
  have hN : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
  have hm0 : (0 : ℝ) < m := by exact_mod_cast h1
  have hmN : (m : ℝ) < nodeCount k := by exact_mod_cast hm
  have hg := Real.goldenRatio_pos
  have hg1 := one_lt_gold'
  have hπ := Real.pi_pos
  have hq : betaRoot k ^ m = Complex.exp (I * ((2 * Real.pi * m / (g * nodeCount k) : ℝ) : ℂ)) := by
    unfold betaRoot
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hqN : (betaRoot k ^ m) ^ nodeCount k =
      Complex.exp (I * ((2 * Real.pi * ((m : ℝ) / g) : ℝ) : ℂ)) := by
    have e : ∀ G : ℝ, G ≠ 0 → (nodeCount k : ℝ) * (2 * Real.pi * m / (G * nodeCount k)) =
        2 * Real.pi * ((m : ℝ) / G) := fun G hG => by field_simp
    rw [hq, ← Complex.exp_nat_mul, ← e g hg.ne']; push_cast; ring_nf
  have hnum : 4 * (1 / (3 * (m : ℝ))) ≤ ‖(betaRoot k ^ m) ^ nodeCount k - 1‖ := by
    rw [hqN]
    exact four_mul_le_norm_exp_sub_one fun n => one_div_three_mul_le_abs_div_gold_sub h1 n
  have hden : ‖betaRoot k ^ m - 1‖ ≤ 2 * Real.pi * m / (g * nodeCount k) := by
    rw [hq]
    refine (norm_exp_I_mul_sub_one_le _).trans (le_of_eq (abs_of_pos (by positivity)))
  have h := le_norm_geom_sum (by positivity) (by positivity) hnum hden
  refine le_trans ?_ h
  have hm2 : (m : ℝ) ^ 2 ≤ (nodeCount k : ℝ) ^ 2 := by nlinarith
  have h3 := pi_mul_three_lt_ten
  have key : ∀ G : ℝ, 1 ≤ G → 1 / (5 * (nodeCount k : ℝ)) ≤
      4 * (1 / (3 * (m : ℝ))) / (2 * Real.pi * m / (G * nodeCount k)) := by
    intro G hG
    have e : 4 * (1 / (3 * (m : ℝ))) / (2 * Real.pi * m / (G * nodeCount k)) =
        2 * G * nodeCount k / (3 * Real.pi * m ^ 2) := by field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : 3 * Real.pi * (m : ℝ) ^ 2 ≤ 10 * (nodeCount k : ℝ) ^ 2 := by nlinarith
    have h5 : 10 * (nodeCount k : ℝ) ^ 2 ≤ 10 * G * (nodeCount k : ℝ) ^ 2 := by nlinarith
    nlinarith
  exact key g hg1.le

/-- `|Γ_k(m)| ≥ 1/(10N_k)` for `1 ≤ m < N_k`. -/
theorem norm_charG_ge (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    1 / (10 * (nodeCount k : ℝ)) ≤ ‖charG k m‖ := by
  have hN : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
  have hm0 : (0 : ℝ) < m := by exact_mod_cast h1
  have hmN : (m : ℝ) < nodeCount k := by exact_mod_cast hm
  have hg := Real.goldenRatio_pos
  have hg2 := gold_lt_two'
  have hπ := Real.pi_pos
  have hq : gammaRoot k ^ m = Complex.exp (I * ((2 * Real.pi * g * m / nodeCount k : ℝ) : ℂ)) := by
    unfold gammaRoot
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hqN : (gammaRoot k ^ m) ^ nodeCount k =
      Complex.exp (I * ((2 * Real.pi * ((m : ℝ) * g) : ℝ) : ℂ)) := by
    have e : ∀ G : ℝ, (nodeCount k : ℝ) * (2 * Real.pi * G * m / nodeCount k) =
        2 * Real.pi * ((m : ℝ) * G) := fun G => by field_simp
    rw [hq, ← Complex.exp_nat_mul, ← e g]; push_cast; ring_nf
  have hnum : 4 * (1 / (3 * (m : ℝ))) ≤ ‖(gammaRoot k ^ m) ^ nodeCount k - 1‖ := by
    rw [hqN]
    exact four_mul_le_norm_exp_sub_one fun n => one_div_three_mul_le_abs_mul_gold_sub h1 n
  have hden : ‖gammaRoot k ^ m - 1‖ ≤ 2 * Real.pi * g * m / nodeCount k := by
    rw [hq]
    refine (norm_exp_I_mul_sub_one_le _).trans (le_of_eq (abs_of_pos (by positivity)))
  have h := le_norm_geom_sum (by positivity) (by positivity) hnum hden
  refine le_trans ?_ h
  have hm2 : (m : ℝ) ^ 2 ≤ (nodeCount k : ℝ) ^ 2 := by nlinarith
  have h3 := pi_mul_three_lt_ten
  have key : ∀ G : ℝ, 0 < G → G < 2 → 1 / (10 * (nodeCount k : ℝ)) ≤
      4 * (1 / (3 * (m : ℝ))) / (2 * Real.pi * G * m / nodeCount k) := by
    intro G hG0 hG
    have e : 4 * (1 / (3 * (m : ℝ))) / (2 * Real.pi * G * m / nodeCount k) =
        2 * nodeCount k / (3 * Real.pi * G * m ^ 2) := by field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : 3 * Real.pi * G * (m : ℝ) ^ 2 ≤ 3 * Real.pi * 2 * (m : ℝ) ^ 2 := by
      have : 0 ≤ 3 * Real.pi * (m : ℝ) ^ 2 := by positivity
      nlinarith
    nlinarith
  exact key g hg hg2

theorem charB_ne_zero (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) : charB k m ≠ 0 := by
  intro h
  have := norm_charB_ge k h1 hm
  rw [h, norm_zero] at this
  have : (0 : ℝ) < 1 / (5 * (nodeCount k : ℝ)) := by
    have : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
    positivity
  linarith

theorem charG_ne_zero (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) : charG k m ≠ 0 := by
  intro h
  have := norm_charG_ge k h1 hm
  rw [h, norm_zero] at this
  have : (0 : ℝ) < 1 / (10 * (nodeCount k : ℝ)) := by
    have : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
    positivity
  linarith

/-! ## Exactness -/

theorem double_sum_mul (f h : ℕ → ℂ) (c : ℂ) (S T : Finset ℕ) :
    ∑ a ∈ S, ∑ b ∈ T, c * (f a * h b) = c * ((∑ a ∈ S, f a) * ∑ b ∈ T, h b) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

theorem sum_uW_mul_root_pow (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    ∑ a ∈ range (nodeCount k), uW k a * (root k ^ m) ^ a = -res1 k m / transfer1 k m := by
  have hN : (nodeCount k : ℂ) ≠ 0 := by exact_mod_cast (nodeCount_pos k).ne'
  calc ∑ a ∈ range (nodeCount k), uW k a * (root k ^ m) ^ a
      = ∑ a ∈ range (nodeCount k), ∑ i ∈ Ico 1 (nodeCount k), 1 / (nodeCount k : ℂ) *
          ((-res1 k i / transfer1 k i) * ((root k ^ m) ^ a / root k ^ (i * a))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        unfold uW
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ i ∈ Ico 1 (nodeCount k), ∑ a ∈ range (nodeCount k), 1 / (nodeCount k : ℂ) *
          ((-res1 k i / transfer1 k i) * ((root k ^ m) ^ a / root k ^ (i * a))) :=
        Finset.sum_comm
    _ = ∑ i ∈ Ico 1 (nodeCount k), 1 / (nodeCount k : ℂ) * (-res1 k i / transfer1 k i) *
          (if m = i then (nodeCount k : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.mul_sum, ← Finset.mul_sum, sum_root_pow_div k hm (Finset.mem_Ico.mp hi).2,
          mul_assoc]
    _ = -res1 k m / transfer1 k m := by
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_Ico.mpr ⟨h1, hm⟩), mul_right_comm,
          one_div_mul_cancel hN, one_mul]

theorem sum_vW_mul_root_pow (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    ∑ b ∈ range (nodeCount k), vW k b * (root k ^ m) ^ b = -res2 k m / transfer2 k m := by
  have hN : (nodeCount k : ℂ) ≠ 0 := by exact_mod_cast (nodeCount_pos k).ne'
  calc ∑ b ∈ range (nodeCount k), vW k b * (root k ^ m) ^ b
      = ∑ b ∈ range (nodeCount k), ∑ i ∈ Ico 1 (nodeCount k), 1 / (nodeCount k : ℂ) *
          ((-res2 k i / transfer2 k i) * ((root k ^ m) ^ b / root k ^ (i * b))) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        unfold vW
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ i ∈ Ico 1 (nodeCount k), ∑ b ∈ range (nodeCount k), 1 / (nodeCount k : ℂ) *
          ((-res2 k i / transfer2 k i) * ((root k ^ m) ^ b / root k ^ (i * b))) :=
        Finset.sum_comm
    _ = ∑ i ∈ Ico 1 (nodeCount k), 1 / (nodeCount k : ℂ) * (-res2 k i / transfer2 k i) *
          (if m = i then (nodeCount k : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.mul_sum, ← Finset.mul_sum, sum_root_pow_div k hm (Finset.mem_Ico.mp hi).2,
          mul_assoc]
    _ = -res2 k m / transfer2 k m := by
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_Ico.mpr ⟨h1, hm⟩), mul_right_comm,
          one_div_mul_cancel hN, one_mul]

theorem prefactor1_ne_zero (k m : ℕ) :
    ((radius k : ℂ) * Complex.exp (I * (height k : ℂ))) ^ m ≠ 0 := by
  apply pow_ne_zero
  apply mul_ne_zero
  · exact_mod_cast (radius_pos k).ne'
  · exact Complex.exp_ne_zero _

theorem prefactor2_ne_zero (k m : ℕ) :
    ((radius2 k : ℂ) * Complex.exp (I * ((g * height k : ℝ) : ℂ))) ^ m ≠ 0 := by
  apply pow_ne_zero
  apply mul_ne_zero
  · exact_mod_cast (radius2_pos k).ne'
  · exact Complex.exp_ne_zero _

/-- **Base `1`: the grid kills the residual moments `1 ≤ m < N_k`.** -/
theorem sum_twoWeight_mul_node1_pow (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    ∑ a ∈ range (nodeCount k), ∑ b ∈ range (nodeCount k), twoWeight k a b * node1 k a b ^ m =
      -res1 k m := by
  set P := ((radius k : ℂ) * Complex.exp (I * (height k : ℂ))) ^ m with hP
  set sh : ℂ := ((twoShift k * twoBound k : ℝ) : ℂ)
  have e : ∀ a b, twoWeight k a b * node1 k a b ^ m =
      P * sh * ((root k ^ m) ^ a * (betaRoot k ^ m) ^ b) +
        P * ((uW k a * (root k ^ m) ^ a) * (betaRoot k ^ m) ^ b) +
        P * ((root k ^ m) ^ a * (vW k b * (betaRoot k ^ m) ^ b)) := by
    intro a b; rw [node1_pow]; unfold twoWeight; ring
  simp_rw [e, Finset.sum_add_distrib]
  rw [double_sum_mul, double_sum_mul (fun a => uW k a * (root k ^ m) ^ a),
    double_sum_mul (fun a => (root k ^ m) ^ a), sum_root_pow k h1 hm, sum_uW_mul_root_pow k h1 hm]
  have hB := charB_ne_zero k h1 hm
  have hP0 : P ≠ 0 := prefactor1_ne_zero k m
  have ht : transfer1 k m = P * charB k m := rfl
  rw [show ∑ b ∈ range (nodeCount k), (betaRoot k ^ m) ^ b = charB k m from rfl, ht]
  field_simp
  ring

/-- **Base `φ`: the grid kills the residual moments `1 ≤ m < N_k`.** -/
theorem sum_twoWeight_mul_node2_pow (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    ∑ a ∈ range (nodeCount k), ∑ b ∈ range (nodeCount k), twoWeight k a b * node2 k a b ^ m =
      -res2 k m := by
  set Q := ((radius2 k : ℂ) * Complex.exp (I * ((g * height k : ℝ) : ℂ))) ^ m with hQ
  set sh : ℂ := ((twoShift k * twoBound k : ℝ) : ℂ)
  have e : ∀ a b, twoWeight k a b * node2 k a b ^ m =
      Q * sh * ((gammaRoot k ^ m) ^ a * (root k ^ m) ^ b) +
        Q * ((uW k a * (gammaRoot k ^ m) ^ a) * (root k ^ m) ^ b) +
        Q * ((gammaRoot k ^ m) ^ a * (vW k b * (root k ^ m) ^ b)) := by
    intro a b; rw [node2_pow]; unfold twoWeight; ring
  simp_rw [e, Finset.sum_add_distrib]
  rw [double_sum_mul, double_sum_mul (fun a => uW k a * (gammaRoot k ^ m) ^ a),
    double_sum_mul (fun a => (gammaRoot k ^ m) ^ a), sum_root_pow k h1 hm,
    sum_vW_mul_root_pow k h1 hm]
  have hG := charG_ne_zero k h1 hm
  have hQ0 : Q ≠ 0 := prefactor2_ne_zero k m
  have ht : transfer2 k m = Q * charG k m := rfl
  rw [show ∑ a ∈ range (nodeCount k), (gammaRoot k ^ m) ^ a = charG k m from rfl, ht]
  field_simp
  ring

theorem res1_succ_eq_zero (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    res1 (k + 1) m = 0 := by
  rw [res1_succ, sum_twoWeight_mul_node1_pow k h1 hm, add_neg_cancel]

theorem res2_succ_eq_zero (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    res2 (k + 1) m = 0 := by
  rw [res2_succ, sum_twoWeight_mul_node2_pow k h1 hm, add_neg_cancel]

/-! ## Bounds -/

theorem norm_prefactor1 (k m : ℕ) :
    ‖((radius k : ℂ) * Complex.exp (I * (height k : ℂ))) ^ m‖ = radius k ^ m := by
  rw [norm_pow, norm_mul, norm_exp_I_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (radius_pos k), mul_one]

theorem norm_prefactor2 (k m : ℕ) :
    ‖((radius2 k : ℂ) * Complex.exp (I * ((g * height k : ℝ) : ℂ))) ^ m‖ = radius2 k ^ m := by
  rw [norm_pow, norm_mul, norm_exp_I_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (radius2_pos k), mul_one]

theorem norm_transfer1_ge (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    radius k ^ m / (5 * (nodeCount k : ℝ)) ≤ ‖transfer1 k m‖ := by
  unfold transfer1
  rw [norm_mul, norm_prefactor1, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (norm_charB_ge k h1 hm) (pow_nonneg (radius_pos k).le _)

theorem norm_transfer2_ge (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    radius2 k ^ m / (10 * (nodeCount k : ℝ)) ≤ ‖transfer2 k m‖ := by
  unfold transfer2
  rw [norm_mul, norm_prefactor2, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (norm_charG_ge k h1 hm) (pow_nonneg (radius2_pos k).le _)

theorem twoBound_nonneg : ∀ k, 0 ≤ twoBound k
  | 0 => by norm_num [twoBound]
  | k + 1 => by
    show 0 ≤ (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k / 2 ^ gainExp k
    have := twoBound_nonneg k
    positivity

/-- The residual bounds of stage `k` in both bases. -/
def ResBound (k : ℕ) : Prop :=
  ∀ m, 1 ≤ m → ‖res1 k m‖ ≤ twoBound k * radius k ^ m ∧ ‖res2 k m‖ ≤ twoBound k * radius2 k ^ m

theorem norm_uW_le {k : ℕ} (h : ResBound k) (a : ℕ) :
    ‖uW k a‖ ≤ 5 * nodeCount k * twoBound k := by
  have hN : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
  have hL := twoBound_nonneg k
  unfold uW
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hterm : ∀ i ∈ Ico 1 (nodeCount k),
      ‖(-res1 k i / transfer1 k i) / root k ^ (i * a)‖ ≤ 5 * nodeCount k * twoBound k := by
    intro i hi
    obtain ⟨hi1, hiN⟩ := Finset.mem_Ico.mp hi
    have ht := norm_transfer1_ge k hi1 hiN
    have hR : 0 < radius k ^ i := pow_pos (radius_pos k) _
    have htpos : 0 < ‖transfer1 k i‖ := lt_of_lt_of_le (by positivity) ht
    rw [norm_div, norm_div, norm_neg, norm_pow, norm_root, one_pow, div_one,
      div_le_iff₀ htpos]
    have hr := (h i hi1).1
    calc ‖res1 k i‖ ≤ twoBound k * radius k ^ i := hr
      _ = 5 * nodeCount k * twoBound k * (radius k ^ i / (5 * (nodeCount k : ℝ))) := by
          field_simp
      _ ≤ 5 * nodeCount k * twoBound k * ‖transfer1 k i‖ :=
          mul_le_mul_of_nonneg_left ht (by positivity)
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ hterm)
  rw [Nat.card_Ico, nsmul_eq_mul] at hsum
  have hcard : ((nodeCount k - 1 : ℕ) : ℝ) ≤ nodeCount k := by exact_mod_cast Nat.sub_le _ _
  calc 1 / (nodeCount k : ℝ) *
        ‖∑ i ∈ Ico 1 (nodeCount k), (-res1 k i / transfer1 k i) / root k ^ (i * a)‖
      ≤ 1 / (nodeCount k : ℝ) * ((nodeCount k : ℝ) * (5 * nodeCount k * twoBound k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = 5 * nodeCount k * twoBound k := by field_simp

theorem norm_vW_le {k : ℕ} (h : ResBound k) (b : ℕ) :
    ‖vW k b‖ ≤ 10 * nodeCount k * twoBound k := by
  have hN : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
  have hL := twoBound_nonneg k
  unfold vW
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hterm : ∀ i ∈ Ico 1 (nodeCount k),
      ‖(-res2 k i / transfer2 k i) / root k ^ (i * b)‖ ≤ 10 * nodeCount k * twoBound k := by
    intro i hi
    obtain ⟨hi1, hiN⟩ := Finset.mem_Ico.mp hi
    have ht := norm_transfer2_ge k hi1 hiN
    have hR : 0 < radius2 k ^ i := pow_pos (radius2_pos k) _
    have htpos : 0 < ‖transfer2 k i‖ := lt_of_lt_of_le (by positivity) ht
    rw [norm_div, norm_div, norm_neg, norm_pow, norm_root, one_pow, div_one,
      div_le_iff₀ htpos]
    have hr := (h i hi1).2
    calc ‖res2 k i‖ ≤ twoBound k * radius2 k ^ i := hr
      _ = 10 * nodeCount k * twoBound k * (radius2 k ^ i / (10 * (nodeCount k : ℝ))) := by
          field_simp
      _ ≤ 10 * nodeCount k * twoBound k * ‖transfer2 k i‖ :=
          mul_le_mul_of_nonneg_left ht (by positivity)
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ hterm)
  rw [Nat.card_Ico, nsmul_eq_mul] at hsum
  have hcard : ((nodeCount k - 1 : ℕ) : ℝ) ≤ nodeCount k := by exact_mod_cast Nat.sub_le _ _
  calc 1 / (nodeCount k : ℝ) *
        ‖∑ i ∈ Ico 1 (nodeCount k), (-res2 k i / transfer2 k i) / root k ^ (i * b)‖
      ≤ 1 / (nodeCount k : ℝ) * ((nodeCount k : ℝ) * (10 * nodeCount k * twoBound k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = 10 * nodeCount k * twoBound k := by field_simp

/-- **Sector and size of the grid weights.** -/
theorem twoWeight_bounds {k : ℕ} (h : ResBound k) (a b : ℕ) :
    15 * (2 ^ k + 2) * nodeCount k * twoBound k ≤ (twoWeight k a b).re ∧
      |(twoWeight k a b).im| ≤ 15 * nodeCount k * twoBound k ∧
      ‖twoWeight k a b‖ ≤ 15 * (2 ^ k + 4) * nodeCount k * twoBound k := by
  have hu := norm_uW_le h a
  have hv := norm_vW_le h b
  have hure := Complex.abs_re_le_norm (uW k a)
  have hvre := Complex.abs_re_le_norm (vW k b)
  have huim := Complex.abs_im_le_norm (uW k a)
  have hvim := Complex.abs_im_le_norm (vW k b)
  have hL := twoBound_nonneg k
  have hN : (0 : ℝ) ≤ nodeCount k := Nat.cast_nonneg _
  have hsh : twoShift k * twoBound k = 15 * (2 ^ k + 3) * nodeCount k * twoBound k := by
    unfold twoShift; ring
  unfold twoWeight
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.add_re, Complex.add_re, Complex.ofReal_re, hsh]
    have := (abs_le.mp hure).1
    have := (abs_le.mp hvre).1
    linarith
  · rw [Complex.add_im, Complex.add_im, Complex.ofReal_im, zero_add]
    refine (abs_add_le _ _).trans ?_
    linarith
  · have hn1 := norm_add_le (((twoShift k * twoBound k : ℝ) : ℂ) + uW k a) (vW k b)
    have hn2 := norm_add_le ((twoShift k * twoBound k : ℝ) : ℂ) (uW k a)
    have hs : ‖((twoShift k * twoBound k : ℝ) : ℂ)‖ =
        15 * (2 ^ k + 3) * nodeCount k * twoBound k := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by rw [hsh]; positivity), hsh]
    linarith

theorem norm_double_sum_le {f : ℕ → ℕ → ℂ} {N : ℕ} {C : ℝ}
    (h : ∀ a ∈ range N, ∀ b ∈ range N, ‖f a b‖ ≤ C) :
    ‖∑ a ∈ range N, ∑ b ∈ range N, f a b‖ ≤ (N : ℝ) * ((N : ℝ) * C) := by
  have hinner : ∀ a ∈ range N, ‖∑ b ∈ range N, f a b‖ ≤ (N : ℝ) * C := by
    intro a ha
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul _ _ _ (h a ha)
    rwa [Finset.card_range, nsmul_eq_mul] at this
  refine (norm_sum_le _ _).trans ?_
  have := Finset.sum_le_card_nsmul _ _ _ hinner
  rwa [Finset.card_range, nsmul_eq_mul] at this

theorem two_pow_mul_radius2_pow_le {k m : ℕ} (hm : nodeCount k ≤ m) :
    (2 : ℝ) ^ gainExp k * radius2 k ^ m ≤ radius2 (k + 1) ^ m := by
  have hθ := one_lt_radiusRatio k
  have hR := radius_pos k
  have hstep : radius2 k * radiusRatio k ≤ radius2 (k + 1) := by
    unfold radius2
    show Real.exp (g * Real.log (radius k)) * radiusRatio k ≤
      Real.exp (g * Real.log (radius k * radiusRatio k))
    rw [Real.log_mul hR.ne' (by linarith), mul_add, Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hl : 0 ≤ Real.log (radiusRatio k) := Real.log_nonneg hθ.le
    calc radiusRatio k = Real.exp (Real.log (radiusRatio k)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (g * Real.log (radiusRatio k)) := by
          apply Real.exp_le_exp.mpr; nlinarith [one_lt_gold']
  have h1 : radiusRatio k ^ nodeCount k ≤ radiusRatio k ^ m := pow_le_pow_right₀ hθ.le hm
  have h2 := two_pow_gainExp_le k
  have h0 : 0 ≤ radius2 k ^ m := pow_nonneg (radius2_pos k).le _
  calc (2 : ℝ) ^ gainExp k * radius2 k ^ m ≤ radiusRatio k ^ m * radius2 k ^ m :=
        mul_le_mul_of_nonneg_right (h2.trans h1) h0
    _ = (radius2 k * radiusRatio k) ^ m := by rw [mul_pow, mul_comm]
    _ ≤ radius2 (k + 1) ^ m :=
        pow_le_pow_left₀ (mul_nonneg (radius2_pos k).le (by linarith)) hstep m

/-- **The residual moments are controlled at every stage, in both bases.** -/
theorem resBound : ∀ k, ResBound k
  | 0 => fun m _ => by
    refine ⟨?_, ?_⟩
    · show ‖(5 / 4 : ℂ) ^ m‖ ≤ 1 * (4 / 3 : ℝ) ^ m
      rw [norm_pow, one_mul, norm_five_fourths]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
    · show ‖((Real.exp (g * Real.log (5 / 4)) : ℝ) : ℂ) ^ m‖ ≤ 1 * radius2 0 ^ m
      rw [norm_pow, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply pow_le_pow_left₀ (Real.exp_pos _).le
      unfold radius2
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ Real.goldenRatio_pos.le
      exact Real.log_le_log (by norm_num) (by norm_num [radius])
  | k + 1 => fun m h1 => by
    have ih := resBound k
    by_cases hm : m < nodeCount k
    · rw [res1_succ_eq_zero k h1 hm, res2_succ_eq_zero k h1 hm, norm_zero]
      exact ⟨mul_nonneg (twoBound_nonneg _) (pow_nonneg (radius_pos _).le _),
        mul_nonneg (twoBound_nonneg _) (pow_nonneg (radius2_pos _).le _)⟩
    · push Not at hm
      have hw := fun a b => (twoWeight_bounds ih a b).2.2
      set W : ℝ := 15 * (2 ^ k + 4) * nodeCount k * twoBound k with hW
      have hW0 : 0 ≤ W := by have := twoBound_nonneg k; positivity
      have hL0 := twoBound_nonneg k
      have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
      have hfac : twoBound k + (nodeCount k : ℝ) * ((nodeCount k : ℝ) * W) =
          (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k := by rw [hW]; ring
      refine ⟨?_, ?_⟩
      · have hsum : ‖∑ a ∈ range (nodeCount k), ∑ b ∈ range (nodeCount k),
            twoWeight k a b * node1 k a b ^ m‖ ≤
            (nodeCount k : ℝ) * ((nodeCount k : ℝ) * (W * radius k ^ m)) := by
          refine norm_double_sum_le fun a _ b _ => ?_
          rw [norm_mul, norm_pow, norm_node1]
          exact mul_le_mul_of_nonneg_right (hw a b) (pow_nonneg (radius_pos k).le _)
        have hgain := two_pow_mul_radius_pow_le hm
        calc ‖res1 (k + 1) m‖
            ≤ ‖res1 k m‖ + ‖∑ a ∈ range (nodeCount k), ∑ b ∈ range (nodeCount k),
                twoWeight k a b * node1 k a b ^ m‖ := by
              rw [res1_succ]; exact norm_add_le _ _
          _ ≤ twoBound k * radius k ^ m +
                (nodeCount k : ℝ) * ((nodeCount k : ℝ) * (W * radius k ^ m)) :=
              add_le_add (ih m h1).1 hsum
          _ = (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k / 2 ^ gainExp k *
                (2 ^ gainExp k * radius k ^ m) := by
              rw [← hfac]; field_simp
          _ ≤ (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k / 2 ^ gainExp k *
                radius (k + 1) ^ m :=
              mul_le_mul_of_nonneg_left hgain (by positivity)
          _ = twoBound (k + 1) * radius (k + 1) ^ m := rfl
      · have hsum : ‖∑ a ∈ range (nodeCount k), ∑ b ∈ range (nodeCount k),
            twoWeight k a b * node2 k a b ^ m‖ ≤
            (nodeCount k : ℝ) * ((nodeCount k : ℝ) * (W * radius2 k ^ m)) := by
          refine norm_double_sum_le fun a _ b _ => ?_
          rw [norm_mul, norm_pow, norm_node2]
          exact mul_le_mul_of_nonneg_right (hw a b) (pow_nonneg (radius2_pos k).le _)
        have hgain := two_pow_mul_radius2_pow_le hm
        calc ‖res2 (k + 1) m‖
            ≤ ‖res2 k m‖ + ‖∑ a ∈ range (nodeCount k), ∑ b ∈ range (nodeCount k),
                twoWeight k a b * node2 k a b ^ m‖ := by
              rw [res2_succ]; exact norm_add_le _ _
          _ ≤ twoBound k * radius2 k ^ m +
                (nodeCount k : ℝ) * ((nodeCount k : ℝ) * (W * radius2 k ^ m)) :=
              add_le_add (ih m h1).2 hsum
          _ = (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k / 2 ^ gainExp k *
                (2 ^ gainExp k * radius2 k ^ m) := by
              rw [← hfac]; field_simp
          _ ≤ (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k / 2 ^ gainExp k *
                radius2 (k + 1) ^ m :=
              mul_le_mul_of_nonneg_left hgain (by positivity)
          _ = twoBound (k + 1) * radius2 (k + 1) ^ m := rfl

/-! ## Explicit decay -/

theorem quadratic_le_four_pow'' (k : ℕ) : 6 * k ^ 2 + 44 * k + 73 ≤ 4 ^ (k + 4) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by ring, pow_succ (4 : ℕ) (k + 4)]
    nlinarith

theorem two_stage_factor_le (k : ℕ) :
    1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4) ≤ 2 ^ (10 * k + 32) := by
  unfold nodeCount
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ 2 ^ (9 * k + 24) := one_le_pow₀ (by norm_num)
  have e1 : ((2 ^ (3 * k + 8) : ℕ) : ℝ) ^ 3 = 2 ^ (9 * k + 24) := by
    push_cast; rw [← pow_mul]; congr 1; ring
  have e2 : (2 : ℝ) ^ (10 * k + 32) = 2 ^ (9 * k + 24) * 2 ^ k * 256 := by
    rw [← pow_add, show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add]; congr 1; ring
  rw [e1, e2]
  nlinarith

theorem twoBound_le_one : ∀ k, twoBound k ≤ 1
  | 0 => by norm_num [twoBound]
  | k + 1 => by
    show (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k / 2 ^ gainExp k ≤ 1
    have hb := twoBound_le_one k
    have hb0 := twoBound_nonneg k
    have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
    rw [div_le_one h2]
    have hexp : 10 * k + 32 ≤ gainExp k := by
      have := quadratic_le_four_pow'' k; unfold gainExp; nlinarith
    have hpow : (2 : ℝ) ^ (10 * k + 32) ≤ 2 ^ gainExp k := pow_le_pow_right₀ (by norm_num) hexp
    have := two_stage_factor_le k
    have hf0 : 0 ≤ 1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4) := by positivity
    calc (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k
        ≤ (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * 1 := mul_le_mul_of_nonneg_left hb hf0
      _ ≤ 2 ^ gainExp k := by linarith

/-- `L_{k+1} ≤ 2^{−((6k+22)(k+1) + 6k + 19)}`. -/
theorem twoBound_succ_le (k : ℕ) :
    twoBound (k + 1) ≤ (1 / 2 : ℝ) ^ ((6 * k + 22) * (k + 1) + 6 * k + 19) := by
  show (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k / 2 ^ gainExp k ≤ _
  set E := (6 * k + 22) * (k + 1) + 6 * k + 19 with hE
  have hexp : E + (10 * k + 32) ≤ gainExp k := by
    have := quadratic_le_four_pow'' k; unfold gainExp; rw [hE]; nlinarith
  have hb := twoBound_le_one k
  have hb0 := twoBound_nonneg k
  have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
  rw [div_le_iff₀ h2, one_div_pow]
  have hpow : (2 : ℝ) ^ (E + (10 * k + 32)) ≤ 2 ^ gainExp k :=
    pow_le_pow_right₀ (by norm_num) hexp
  rw [pow_add] at hpow
  have h2E : (0 : ℝ) < 2 ^ E := by positivity
  have := two_stage_factor_le k
  have hf0 : 0 ≤ 1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4) := by positivity
  calc (1 + 15 * (nodeCount k : ℝ) ^ 3 * (2 ^ k + 4)) * twoBound k ≤ 2 ^ (10 * k + 32) := by
        nlinarith
    _ = 1 / 2 ^ E * (2 ^ E * 2 ^ (10 * k + 32)) := by field_simp
    _ ≤ 1 / 2 ^ E * 2 ^ gainExp k := mul_le_mul_of_nonneg_left hpow (by positivity)

/-! ## The configuration -/

/-- Stage sizes per axis: one base point, then `N_k × N_k` grids. -/
def cnt : ℕ → ℕ
  | 0 => 1
  | k + 1 => nodeCount k

/-- The index type. -/
abbrev Idx2 := Σ k : ℕ, Fin (cnt k) × Fin (cnt k)

/-- Grid ordinates `T_k + 2πa/N_k + 2πb/(φN_k)`. -/
def ordinate (k a b : ℕ) : ℝ :=
  height k + 2 * Real.pi * a / nodeCount k + 2 * Real.pi * b / (g * nodeCount k)

/-- The points. -/
def zpt : Idx2 → ℂ
  | ⟨0, _⟩ => (Real.log (5 / 4) : ℂ)
  | ⟨k + 1, (a, b)⟩ => (Real.log (radius k) : ℂ) + I * (ordinate k a b : ℂ)

/-- The weights. -/
def wt : Idx2 → ℂ
  | ⟨0, _⟩ => 1
  | ⟨k + 1, (a, b)⟩ => twoWeight k a b

/-- The base index. -/
def base2 : Idx2 := ⟨0, (⟨0, by norm_num [cnt]⟩, ⟨0, by norm_num [cnt]⟩)⟩

theorem exp_zpt_succ (k : ℕ) (a b : Fin (cnt (k + 1))) :
    Complex.exp (zpt ⟨k + 1, (a, b)⟩) = node1 k a b := by
  have hN : (nodeCount k : ℂ) ≠ 0 := by exact_mod_cast (nodeCount_pos k).ne'
  have e : zpt ⟨k + 1, (a, b)⟩ = (Real.log (radius k) : ℂ) + I * (height k : ℂ) +
      (a : ℂ) * (2 * Real.pi * I / (nodeCount k : ℂ)) +
      (b : ℂ) * (I * ((2 * Real.pi / (g * nodeCount k) : ℝ) : ℂ)) := by
    show (Real.log (radius k) : ℂ) + I * (ordinate k a b : ℂ) = _
    unfold ordinate
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul,
    Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log (radius_pos k)]
  rfl

theorem exp_gold_mul_zpt_succ (k : ℕ) (a b : Fin (cnt (k + 1))) :
    Complex.exp (g * zpt ⟨k + 1, (a, b)⟩) = node2 k a b := by
  have hN : (nodeCount k : ℝ) ≠ 0 := by exact_mod_cast (nodeCount_pos k).ne'
  have hcancel : ∀ G : ℝ, G ≠ 0 →
      G * (2 * Real.pi * b / (G * nodeCount k)) = 2 * Real.pi * b / nodeCount k :=
    fun G hG => by field_simp
  have e : (g : ℂ) * zpt ⟨k + 1, (a, b)⟩ = ((g * Real.log (radius k) : ℝ) : ℂ) +
      I * ((g * height k : ℝ) : ℂ) + (a : ℂ) * (I * ((2 * Real.pi * g / nodeCount k : ℝ) : ℂ)) +
      (b : ℂ) * (2 * Real.pi * I / (nodeCount k : ℂ)) := by
    show (g : ℂ) * ((Real.log (radius k) : ℂ) + I * (ordinate k a b : ℂ)) = _
    have ho : g * ordinate k a b = g * height k + 2 * Real.pi * g / nodeCount k * a +
        2 * Real.pi * b / nodeCount k := by
      unfold ordinate
      rw [mul_add, mul_add, hcancel g Real.goldenRatio_ne_zero]
      ring
    have ho' : (g : ℂ) * (ordinate k a b : ℂ) = ((g * height k : ℝ) : ℂ) +
        ((2 * Real.pi * g / nodeCount k : ℝ) : ℂ) * a + 2 * Real.pi * b / (nodeCount k : ℂ) := by
      rw [← Complex.ofReal_mul, ho]; push_cast; ring
    calc (g : ℂ) * ((Real.log (radius k) : ℂ) + I * (ordinate k a b : ℂ))
        = ((g * Real.log (radius k) : ℝ) : ℂ) + I * ((g : ℂ) * (ordinate k a b : ℂ)) := by
          push_cast; ring
      _ = _ := by rw [ho']; ring
  rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul,
    Complex.exp_nat_mul, ← Complex.ofReal_exp]
  rfl

theorem exp_zpt_zero (j : Fin (cnt 0) × Fin (cnt 0)) :
    Complex.exp (zpt ⟨0, j⟩) = 5 / 4 := by
  show Complex.exp (Real.log (5 / 4) : ℂ) = 5 / 4
  rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]; push_cast; ring

theorem exp_gold_mul_zpt_zero (j : Fin (cnt 0) × Fin (cnt 0)) :
    Complex.exp (g * zpt ⟨0, j⟩) = ((Real.exp (g * Real.log (5 / 4)) : ℝ) : ℂ) := by
  show Complex.exp ((g : ℂ) * (Real.log (5 / 4) : ℂ)) = _
  rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]

/-! ### Moments -/

/-- Base-`1` moment contribution of stage `k`. -/
def stage1 (m k : ℕ) : ℂ :=
  ∑ j : Fin (cnt k) × Fin (cnt k), wt ⟨k, j⟩ * Complex.exp (zpt ⟨k, j⟩) ^ m

/-- Base-`φ` moment contribution of stage `k`. -/
def stage2 (m k : ℕ) : ℂ :=
  ∑ j : Fin (cnt k) × Fin (cnt k), wt ⟨k, j⟩ * Complex.exp (g * zpt ⟨k, j⟩) ^ m

theorem stage1_succ (m k : ℕ) : stage1 m (k + 1) = res1 (k + 1) m - res1 k m := by
  unfold stage1
  rw [res1_succ, add_sub_cancel_left, Fintype.sum_prod_type]
  simp only [exp_zpt_succ]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range (nodeCount k),
    twoWeight k a b * node1 k a b ^ m)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun b => twoWeight k a b * node1 k a b ^ m) (nodeCount k)

theorem stage2_succ (m k : ℕ) : stage2 m (k + 1) = res2 (k + 1) m - res2 k m := by
  unfold stage2
  rw [res2_succ, add_sub_cancel_left, Fintype.sum_prod_type]
  simp only [exp_gold_mul_zpt_succ]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range (nodeCount k),
    twoWeight k a b * node2 k a b ^ m)]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun b => twoWeight k a b * node2 k a b ^ m) (nodeCount k)

theorem stage1_zero (m : ℕ) : stage1 m 0 = res1 0 m := by
  unfold stage1
  have hterm : ∀ j : Fin (cnt 0) × Fin (cnt 0),
      wt ⟨0, j⟩ * Complex.exp (zpt ⟨0, j⟩) ^ m = res1 0 m := by
    intro j
    rw [exp_zpt_zero]
    show (1 : ℂ) * (5 / 4 : ℂ) ^ m = (5 / 4 : ℂ) ^ m
    ring
  have hc : Fintype.card (Fin (cnt 0) × Fin (cnt 0)) = 1 := rfl
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ, hc, one_smul]

theorem stage2_zero (m : ℕ) : stage2 m 0 = res2 0 m := by
  unfold stage2
  have hterm : ∀ j : Fin (cnt 0) × Fin (cnt 0),
      wt ⟨0, j⟩ * Complex.exp (g * zpt ⟨0, j⟩) ^ m = res2 0 m := by
    intro j
    rw [exp_gold_mul_zpt_zero]
    show (1 : ℂ) * ((Real.exp (g * Real.log (5 / 4)) : ℝ) : ℂ) ^ m =
      ((Real.exp (g * Real.log (5 / 4)) : ℝ) : ℂ) ^ m
    ring
  have hc : Fintype.card (Fin (cnt 0) × Fin (cnt 0)) = 1 := rfl
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_const, Finset.card_univ, hc, one_smul]

theorem sum_range_stage1 (m K : ℕ) : ∑ k ∈ range (K + 1), stage1 m k = res1 K m := by
  induction K with
  | zero => simp [stage1_zero]
  | succ K ih => rw [Finset.sum_range_succ, ih, stage1_succ]; ring

theorem sum_range_stage2 (m K : ℕ) : ∑ k ∈ range (K + 1), stage2 m k = res2 K m := by
  induction K with
  | zero => simp [stage2_zero]
  | succ K ih => rw [Finset.sum_range_succ, ih, stage2_succ]; ring

theorem lt_nodeCount_of_le {m k : ℕ} (hk : m ≤ k) : m < nodeCount k := by
  unfold nodeCount
  calc m ≤ k := hk
    _ < 2 ^ k := Nat.lt_two_pow_self
    _ ≤ 2 ^ (3 * k + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem hasSum_stage1 {m : ℕ} (h1 : 1 ≤ m) : HasSum (stage1 m) 0 := by
  have hzero : ∀ k ∉ range (m + 2), stage1 m k = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [stage1_succ, res1_succ_eq_zero k' h1 (lt_nodeCount_of_le (by omega))]
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    rw [res1_succ_eq_zero k'' h1 (lt_nodeCount_of_le (by omega)), sub_zero]
  have h : HasSum (stage1 m) (∑ b ∈ range (m + 2), stage1 m b) :=
    hasSum_sum_of_ne_finset_zero hzero
  rwa [sum_range_stage1, res1_succ_eq_zero m h1 (lt_nodeCount_of_le le_rfl)] at h

theorem hasSum_stage2 {m : ℕ} (h1 : 1 ≤ m) : HasSum (stage2 m) 0 := by
  have hzero : ∀ k ∉ range (m + 2), stage2 m k = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [stage2_succ, res2_succ_eq_zero k' h1 (lt_nodeCount_of_le (by omega))]
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    rw [res2_succ_eq_zero k'' h1 (lt_nodeCount_of_le (by omega)), sub_zero]
  have h : HasSum (stage2 m) (∑ b ∈ range (m + 2), stage2 m b) :=
    hasSum_sum_of_ne_finset_zero hzero
  rwa [sum_range_stage2, res2_succ_eq_zero m h1 (lt_nodeCount_of_le le_rfl)] at h

/-! ### Geometry of the points -/

theorem re_zpt_succ (k : ℕ) (j : Fin (cnt (k + 1)) × Fin (cnt (k + 1))) :
    (zpt ⟨k + 1, j⟩).re = Real.log (radius k) := by
  obtain ⟨a, b⟩ := j
  simp [zpt]

theorem im_zpt_succ (k : ℕ) (j : Fin (cnt (k + 1)) × Fin (cnt (k + 1))) :
    (zpt ⟨k + 1, j⟩).im = ordinate k j.1 j.2 := by
  obtain ⟨a, b⟩ := j
  simp [zpt]

theorem re_zpt_zero (j : Fin (cnt 0) × Fin (cnt 0)) : (zpt ⟨0, j⟩).re = Real.log (5 / 4) := by
  show ((Real.log (5 / 4) : ℝ) : ℂ).re = _
  rw [Complex.ofReal_re]

theorem im_zpt_zero (j : Fin (cnt 0) × Fin (cnt 0)) : (zpt ⟨0, j⟩).im = 0 := by
  show ((Real.log (5 / 4) : ℝ) : ℂ).im = _
  rw [Complex.ofReal_im]

theorem log_five_fourths_lt_log_radius (k : ℕ) : Real.log (5 / 4) < Real.log (radius k) :=
  Real.log_lt_log (by norm_num) (by linarith [four_thirds_le_radius k])

theorem re_zpt_bounds (i : Idx2) :
    Real.log (5 / 4) ≤ (zpt i).re ∧ (zpt i).re ≤ Real.log 10 := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero => rw [re_zpt_zero]; exact ⟨le_rfl, Real.log_le_log (by norm_num) (by norm_num)⟩
  | succ k =>
    rw [re_zpt_succ]
    exact ⟨(log_five_fourths_lt_log_radius k).le,
      Real.log_le_log (radius_pos k) (radius_le_ten k)⟩

theorem exists_re_zpt_gt (i : Idx2) : ∃ j : Idx2, (zpt i).re < (zpt j).re := by
  obtain ⟨k, j⟩ := i
  have hfin : ∀ k : ℕ, 0 < cnt (k + 1) := fun k => nodeCount_pos k
  cases k with
  | zero =>
    refine ⟨⟨1, (⟨0, hfin 0⟩, ⟨0, hfin 0⟩)⟩, ?_⟩
    rw [re_zpt_zero, re_zpt_succ]
    exact log_five_fourths_lt_log_radius 0
  | succ k =>
    refine ⟨⟨k + 2, (⟨0, hfin (k + 1)⟩, ⟨0, hfin (k + 1)⟩)⟩, ?_⟩
    rw [re_zpt_succ, re_zpt_succ]
    exact Real.log_lt_log (radius_pos k) (radius_lt_succ k)

theorem height_le_ordinate (k a b : ℕ) : height k ≤ ordinate k a b := by
  unfold ordinate
  have hN : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
  have h1 : 0 ≤ 2 * Real.pi * a / nodeCount k := by positivity
  have h2 : 0 ≤ 2 * Real.pi * b / (g * nodeCount k) := by
    have := Real.goldenRatio_pos; positivity
  linarith

theorem finite_im_zpt_le (T : ℝ) : {i : Idx2 | |(zpt i).im| ≤ T}.Finite := by
  obtain ⟨K, hK⟩ := exists_nat_gt (T / 20)
  refine (((Finset.range (K + 1)).sigma fun k =>
    (Finset.univ : Finset (Fin (cnt k) × Fin (cnt k)))).finite_toSet).subset fun i hi => ?_
  obtain ⟨k, j⟩ := i
  simp only [Set.mem_setOf_eq] at hi
  simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio, Finset.coe_univ,
    Set.mem_univ, and_true]
  cases k with
  | zero => omega
  | succ k =>
    rw [im_zpt_succ] at hi
    have hh := height_le_ordinate k j.1 j.2
    have hle := (abs_le.mp hi).2
    have : (20 : ℝ) * ((k : ℝ) + 1) < 20 * K := by
      unfold height at hh; rw [div_lt_iff₀ (by norm_num)] at hK; linarith
    have : (k : ℝ) + 1 < K := by linarith
    have : k + 1 < K := by exact_mod_cast this
    omega

theorem mul_sub_eq_of_grid_eq {G T N a₁ b₁ a₂ b₂ : ℝ} (hG : 0 < G) (hN : 0 < N)
    (h : T + 2 * Real.pi * a₁ / N + 2 * Real.pi * b₁ / (G * N) =
      T + 2 * Real.pi * a₂ / N + 2 * Real.pi * b₂ / (G * N)) :
    (a₁ - a₂) * G = b₂ - b₁ := by
  have hπ := Real.pi_pos
  have e : T + 2 * Real.pi * a₁ / N + 2 * Real.pi * b₁ / (G * N) -
      (T + 2 * Real.pi * a₂ / N + 2 * Real.pi * b₂ / (G * N)) =
        2 * Real.pi / (G * N) * ((a₁ - a₂) * G - (b₂ - b₁)) := by
    field_simp; ring
  rw [h, sub_self] at e
  have hne : 2 * Real.pi / (G * N) ≠ 0 := by positivity
  have := (mul_eq_zero.mp e.symm).resolve_left hne
  linarith

/-- `a + b/φ` determines `(a, b)`. -/
theorem eq_of_ordinate_eq {k : ℕ} {a₁ b₁ a₂ b₂ : ℕ} (h : ordinate k a₁ b₁ = ordinate k a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  have hN : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
  have key := mul_sub_eq_of_grid_eq Real.goldenRatio_pos hN h
  by_cases ha : a₁ = a₂
  · subst ha
    refine ⟨rfl, ?_⟩
    have : ((b₂ : ℝ) - b₁) = 0 := by rw [← key]; ring
    have : (b₁ : ℝ) = b₂ := by linarith
    exact_mod_cast this
  · exfalso
    have hne : ((a₁ : ℝ) - a₂) ≠ 0 := by
      intro h0; apply ha; have : (a₁ : ℝ) = a₂ := by linarith
      exact_mod_cast this
    apply Real.goldenRatio_irrational
    refine ⟨((b₂ : ℚ) - b₁) / ((a₁ : ℚ) - a₂), ?_⟩
    push_cast
    rw [div_eq_iff hne, mul_comm]
    exact key.symm

theorem zpt_injective : Function.Injective zpt := by
  rintro ⟨ka, ja⟩ ⟨kb, jb⟩ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  cases ka with
  | zero =>
    cases kb with
    | zero =>
      congr
      exact Subsingleton.elim (α := Fin 1 × Fin 1) _ _
    | succ kb =>
      exfalso
      rw [re_zpt_zero, re_zpt_succ] at hre
      exact (log_five_fourths_lt_log_radius kb).ne hre
  | succ ka =>
    cases kb with
    | zero =>
      exfalso
      rw [re_zpt_zero, re_zpt_succ] at hre
      exact (log_five_fourths_lt_log_radius ka).ne hre.symm
    | succ kb =>
      rw [re_zpt_succ, re_zpt_succ] at hre
      have hk : ka = kb := strictMono_radius.injective
        (Real.log_injOn_pos (Set.mem_Ioi.mpr (radius_pos ka)) (Set.mem_Ioi.mpr (radius_pos kb)) hre)
      subst hk
      rw [im_zpt_succ, im_zpt_succ] at him
      obtain ⟨h1, h2⟩ := eq_of_ordinate_eq him
      have e1 : ja.1 = jb.1 := Fin.ext h1
      have e2 : ja.2 = jb.2 := Fin.ext h2
      have : ja = jb := Prod.ext e1 e2
      subst this
      rfl

/-! ### The weights -/

theorem wt_sector (i : Idx2) : ‖wt i‖ ≤ 2 * (wt i).re := by
  obtain ⟨k, a, b⟩ := i
  cases k with
  | zero => show ‖(1 : ℂ)‖ ≤ 2 * (1 : ℂ).re; simp
  | succ k =>
    show ‖twoWeight k a b‖ ≤ 2 * (twoWeight k a b).re
    obtain ⟨hre, -, hn⟩ := twoWeight_bounds (resBound k) a b
    have hL := twoBound_nonneg k
    have hN : (0 : ℝ) ≤ nodeCount k := Nat.cast_nonneg _
    have hp : (0 : ℝ) ≤ 2 ^ k := by positivity
    nlinarith [mul_nonneg (mul_nonneg hp hN) hL, mul_nonneg hN hL]

theorem finite_wt_arg {ε : ℝ} (hε : 0 < ε) : {i : Idx2 | ε * (wt i).re < |(wt i).im|}.Finite := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 / ε < 2 ^ K := pow_unbounded_of_one_lt _ (by norm_num)
  refine (((Finset.range (K + 1)).sigma fun k =>
    (Finset.univ : Finset (Fin (cnt k) × Fin (cnt k)))).finite_toSet).subset fun i hi => ?_
  obtain ⟨k, a, b⟩ := i
  simp only [Set.mem_setOf_eq] at hi
  simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio, Finset.coe_univ,
    Set.mem_univ, and_true]
  by_contra hk
  push Not at hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hi' : ε * (twoWeight k' a b).re < |(twoWeight k' a b).im| := hi
  obtain ⟨hre, him, -⟩ := twoWeight_bounds (resBound k') a b
  have hpow : (2 : ℝ) ^ K ≤ 2 ^ k' := pow_le_pow_right₀ (by norm_num) (by omega)
  have hL := twoBound_nonneg k'
  have hN : (0 : ℝ) ≤ nodeCount k' := Nat.cast_nonneg _
  have hX : 0 ≤ 15 * (nodeCount k' : ℝ) * twoBound k' := by positivity
  have hεk : 1 ≤ ε * (2 ^ k' + 2) := by
    rw [div_lt_iff₀ hε] at hK; nlinarith
  have : 15 * (nodeCount k' : ℝ) * twoBound k' ≤ ε * (twoWeight k' a b).re := by
    calc 15 * (nodeCount k' : ℝ) * twoBound k'
        ≤ ε * (2 ^ k' + 2) * (15 * (nodeCount k' : ℝ) * twoBound k') := by nlinarith
      _ = ε * (15 * (2 ^ k' + 2) * nodeCount k' * twoBound k') := by ring
      _ ≤ ε * (twoWeight k' a b).re := mul_le_mul_of_nonneg_left hre hε.le
  linarith

theorem norm_wt_le_stage (k : ℕ) (j : Fin (cnt (k + 1)) × Fin (cnt (k + 1))) :
    ‖wt ⟨k + 1, j⟩‖ ≤ 15 * (2 ^ k + 4) * nodeCount k * twoBound k :=
  (twoWeight_bounds (resBound k) j.1 j.2).2.2

theorem summable_two_stage_rpow {p : ℝ} (hp : 0 < p) :
    Summable fun k : ℕ => ((nodeCount (k + 1) : ℝ) ^ 2) *
      (15 * (2 ^ (k + 1) + 4) * nodeCount (k + 1) * twoBound (k + 1)) ^ p := by
  have hq0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * p) := by positivity
  have hq1 : (1 / 2 : ℝ) ^ (2 * p) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hq0 hq1) ?_
  filter_upwards [eventually_ge_atTop ⌈1 / p⌉₊] with k hk
  have hkp : 1 ≤ p * ((k : ℝ) + 1) := by
    have h1 : 1 / p ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have h2 : 1 / p * p = 1 := by field_simp
    nlinarith
  have hb0 := twoBound_nonneg (k + 1)
  set E : ℕ := (6 * k + 22) * (k + 1) + 6 * k + 19 with hE
  have hbE := twoBound_succ_le k
  have hfac : 15 * (2 ^ (k + 1) + 4) * (nodeCount (k + 1) : ℝ) ≤
      (2 : ℝ) ^ ((4 * k + 19 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    unfold nodeCount
    have h1 : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
    have e : (2 : ℝ) ^ (4 * k + 19) = 2 ^ (k + 1) * 2 ^ (3 * (k + 1) + 8) * 128 := by
      rw [← pow_add, show (128 : ℝ) = 2 ^ 7 by norm_num, ← pow_add]; congr 1; ring
    rw [e]
    push_cast
    have h3 : (0 : ℝ) ≤ 2 ^ (3 * (k + 1) + 8) := by positivity
    nlinarith
  have hfac0 : 0 ≤ 15 * (2 ^ (k + 1) + 4) * (nodeCount (k + 1) : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hprod : 15 * (2 ^ (k + 1) + 4) * (nodeCount (k + 1) : ℝ) * twoBound (k + 1) ≤
      (2 : ℝ) ^ ((4 * k + 19 : ℕ) : ℝ) * (2 : ℝ) ^ (-(E : ℝ)) := by
    have : (1 / 2 : ℝ) ^ E = (2 : ℝ) ^ (-(E : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
    rw [← this]
    exact mul_le_mul hfac hbE hb0 (by positivity)
  have h1 : (15 * (2 ^ (k + 1) + 4) * (nodeCount (k + 1) : ℝ) * twoBound (k + 1)) ^ p ≤
      ((2 : ℝ) ^ ((4 * k + 19 : ℕ) : ℝ) * (2 : ℝ) ^ (-(E : ℝ))) ^ p :=
    Real.rpow_le_rpow (mul_nonneg hfac0 hb0) hprod hp.le
  have h2 : ((2 : ℝ) ^ ((4 * k + 19 : ℕ) : ℝ) * (2 : ℝ) ^ (-(E : ℝ))) ^ p =
      (2 : ℝ) ^ ((((4 * k + 19 : ℕ) : ℝ) + -(E : ℝ)) * p) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_mul (by norm_num)]
  have h3 : ((nodeCount (k + 1) : ℝ) ^ 2) = (2 : ℝ) ^ ((6 * k + 22 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; unfold nodeCount; push_cast; rw [← pow_mul]; congr 1; ring
  have h4 : ((1 / 2 : ℝ) ^ (2 * p)) ^ k = (2 : ℝ) ^ (-(2 * p * k)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num)]
  rw [h4]
  calc ((nodeCount (k + 1) : ℝ) ^ 2) *
        (15 * (2 ^ (k + 1) + 4) * nodeCount (k + 1) * twoBound (k + 1)) ^ p
      ≤ ((nodeCount (k + 1) : ℝ) ^ 2) * (2 : ℝ) ^ ((((4 * k + 19 : ℕ) : ℝ) + -(E : ℝ)) * p) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (2 : ℝ) ^ (((6 * k + 22 : ℕ) : ℝ) + (((4 * k + 19 : ℕ) : ℝ) + -(E : ℝ)) * p) := by
        rw [h3, ← Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ (-(2 * p * k)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hE]
        push_cast
        nlinarith

theorem summable_norm_wt_rpow {p : ℝ} (hp : 0 < p) : Summable fun i : Idx2 => ‖wt i‖ ^ p := by
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  refine ⟨fun k => Summable.of_finite, ?_⟩
  rw [← summable_nat_add_iff 1]
  have hstage : ∀ k : ℕ, ∑' j : Fin (cnt (k + 1)) × Fin (cnt (k + 1)), ‖wt ⟨k + 1, j⟩‖ ^ p ≤
      ((nodeCount k : ℝ) ^ 2) * (15 * (2 ^ k + 4) * nodeCount k * twoBound k) ^ p := by
    intro k
    rw [tsum_fintype]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (cnt (k + 1)) × Fin (cnt (k + 1)))),
        ‖wt ⟨k + 1, j⟩‖ ^ p ≤ (15 * (2 ^ k + 4) * nodeCount k * twoBound k) ^ p := fun j _ =>
      Real.rpow_le_rpow (norm_nonneg _) (norm_wt_le_stage k j) hp.le
    have := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul] at this
    calc _ ≤ ((cnt (k + 1) * cnt (k + 1) : ℕ) : ℝ) *
          (15 * (2 ^ k + 4) * nodeCount k * twoBound k) ^ p :=
          this
      _ = _ := by show ((nodeCount k * nodeCount k : ℕ) : ℝ) * _ = _; push_cast; ring
  refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => by positivity) hstage ?_
  rw [← summable_nat_add_iff 1]
  exact summable_two_stage_rpow hp

theorem summable_norm_wt : Summable fun i : Idx2 => ‖wt i‖ := by
  simpa using summable_norm_wt_rpow (p := 1) one_pos

/-! ### Vanishing moments -/

theorem norm_exp_zpt_le (i : Idx2) : ‖Complex.exp (zpt i)‖ ≤ 10 := by
  rw [Complex.norm_exp]
  calc Real.exp (zpt i).re ≤ Real.exp (Real.log 10) := Real.exp_le_exp.mpr (re_zpt_bounds i).2
    _ = 10 := Real.exp_log (by norm_num)

theorem norm_exp_gold_mul_zpt_le (i : Idx2) : ‖Complex.exp (g * zpt i)‖ ≤ 100 := by
  rw [Complex.norm_exp]
  have hre : ((g : ℂ) * zpt i).re = g * (zpt i).re := by simp
  rw [hre]
  have h1 := (re_zpt_bounds i).2
  have h0 : 0 ≤ (zpt i).re :=
    le_trans (Real.log_nonneg (by norm_num)) (re_zpt_bounds i).1
  have hl : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  calc Real.exp (g * (zpt i).re) ≤ Real.exp (2 * Real.log 10) := by
        apply Real.exp_le_exp.mpr; nlinarith [gold_lt_two', Real.goldenRatio_pos]
    _ = 100 := by rw [show (2 : ℝ) * Real.log 10 = Real.log (10 ^ 2) by rw [Real.log_pow]; norm_num,
          Real.exp_log (by norm_num)]; norm_num

theorem hasSum_wt_exp {m : ℕ} (h1 : 1 ≤ m) :
    HasSum (fun i : Idx2 => wt i * Complex.exp (m * zpt i)) 0 := by
  have hsum : Summable fun i : Idx2 => wt i * Complex.exp (m * zpt i) := by
    refine Summable.of_norm_bounded (summable_norm_wt.mul_right ((10 : ℝ) ^ m)) fun i => ?_
    rw [norm_mul, Complex.exp_nat_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_exp_zpt_le i) m)
      (norm_nonneg _)
  have hσ := hsum.hasSum.sigma
    (fun k => hasSum_fintype (fun j => wt ⟨k, j⟩ * Complex.exp (m * zpt ⟨k, j⟩)))
  have heq : (fun k => ∑ j, wt ⟨k, j⟩ * Complex.exp (m * zpt ⟨k, j⟩)) = stage1 m := by
    funext k; unfold stage1; simp only [Complex.exp_nat_mul]
  rw [heq] at hσ
  rw [← hσ.unique (hasSum_stage1 h1)]
  exact hsum.hasSum

theorem hasSum_wt_exp_gold {m : ℕ} (h1 : 1 ≤ m) :
    HasSum (fun i : Idx2 => wt i * Complex.exp (m * (g * zpt i))) 0 := by
  have hsum : Summable fun i : Idx2 => wt i * Complex.exp (m * (g * zpt i)) := by
    refine Summable.of_norm_bounded (summable_norm_wt.mul_right ((100 : ℝ) ^ m)) fun i => ?_
    rw [norm_mul, Complex.exp_nat_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_exp_gold_mul_zpt_le i) m) (norm_nonneg _)
  have hσ := hsum.hasSum.sigma
    (fun k => hasSum_fintype (fun j => wt ⟨k, j⟩ * Complex.exp (m * (g * zpt ⟨k, j⟩))))
  have heq : (fun k => ∑ j, wt ⟨k, j⟩ * Complex.exp (m * (g * zpt ⟨k, j⟩))) = stage2 m := by
    funext k; unfold stage2; simp only [Complex.exp_nat_mul]
  rw [heq] at hσ
  rw [← hσ.unique (hasSum_stage2 h1)]
  exact hsum.hasSum

/-- **A two-base Wolff configuration with sector weights.** For the golden ratio `φ` there is a
countable family of distinct, locally finite points `z_i` with `log(5/4) ≤ Re z_i ≤ log 10` and no
largest real part, with weights in the sector `|c_i| ≤ 2 Re c_i` whose arguments tend to `0`, one
weight equal to `1`, and `Σ|c_i|^p < ∞` for every `p > 0`, such that
`Σ_i c_i e^{m z_i} = Σ_i c_i e^{m φ z_i} = 0` for every `m ≥ 1`. -/
theorem exists_two_base_sector_configuration :
    ∃ (ι : Type) (_ : Countable ι) (z : ι → ℂ) (c : ι → ℂ), Function.Injective z ∧
      (∀ i, Real.log (5 / 4) ≤ (z i).re ∧ (z i).re ≤ Real.log 10) ∧
      (∀ i, ∃ j, (z i).re < (z j).re) ∧
      (∀ T : ℝ, {i | |(z i).im| ≤ T}.Finite) ∧
      (∃ i, c i = 1) ∧ (∀ i, ‖c i‖ ≤ 2 * (c i).re) ∧
      (∀ ε : ℝ, 0 < ε → {i | ε * (c i).re < |(c i).im|}.Finite) ∧
      (∀ p : ℝ, 0 < p → Summable fun i => ‖c i‖ ^ p) ∧
      ∀ m : ℕ, 1 ≤ m → HasSum (fun i => c i * Complex.exp (m * z i)) 0 ∧
        HasSum (fun i => c i * Complex.exp (m * (g * z i))) 0 :=
  ⟨Idx2, inferInstance, zpt, wt, zpt_injective, re_zpt_bounds, exists_re_zpt_gt,
    finite_im_zpt_le, ⟨base2, rfl⟩, wt_sector, fun _ hε => finite_wt_arg hε,
    fun _ hp => summable_norm_wt_rpow hp, fun _ hm => ⟨hasSum_wt_exp hm, hasSum_wt_exp_gold hm⟩⟩

end

end GaloisForLFunctions.HTGeometry.TwoBaseQuadrature
