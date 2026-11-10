import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheDegreePointsCarryWeilsArchimedeanDiagonal
import GaloisForLFunctions.HyperbolicArakelovTheory.TheFinitePartOfTheCoupledAdelicOrbit

/-!
# The density of the carrier is Weil's constant

The coupled orbit of the adelic carrier sums the products of the local critical Green profiles
over the reduced rational displacements `a/n`. Its rows are renormalized by two counterterms, the
collision row and the density row `c₀·φ(n)/n²`, `c₀ = log 2/4 + π/8`. This file reads the rows on
the comb of the square degree points `n²` of the arithmetic square, where the point `n²` has the
mass `2/n`.

* **The rows are jets of square degrees** (`geometricRow_eq_sum_jetKernel`): the term of the
  carrier at `a/n` is `Γ_{a²} ·_∞ Γ_{n²}/(an)²`.
* **The comb of squares** (`squareWeight_eq_archLevyDensity`, `squareRow_eq`,
  `tendsto_squareRow_sub_log`): the rate of the jump `n² → m²` is `(2/m)·ω(2|log(m/n)|)`, with `ω`
  the Lévy density of Weil's archimedean form; the total rate is
  `H_{2n} − 3/(4n) + Σ_{m ≠ n} n/(m² + n²)`; minus `log(n/4π)`, the counterterm of a comb of density
  `n/2`, it tends to `−A(0)`.
* **Half a row of the carrier** (`sum_squareWeight_below`, `abs_sum_squareWeight_below_sub_le`):
  the rates into the points below `n²` sum to `½H_{n−1} + (2/n)(smoothRow n − 3/8)`: the collision
  term `½H_{n−1}` plus the density term `2c₀`, up to `9/(4n)`.
* **The two counterterms are the mesh and Weil's constant** (`tendsto_counterterms_sub`,
  `tendsto_squareRow_sub_counterterms`): `H_{n−1} + 4c₀ − (log(n/4π) − A(0)) → 0`, and the total
  rate minus `H_{n−1} + 4c₀` tends to `0`.

So `−A(0) = 4c₀ + γ + log 4π` term by term: `4c₀` is the density row, `γ` the constant of the
harmonic collision row, `log 4π` the mesh constant of the comb of squares. The subtraction of the
carrier removes the counterterm of the comb together with Weil's constant. Weil's diagonal is the
density of the orbit sum; the finite part of the orbit is a sum of quadrature errors and contains
no diagonal.
-/

open Finset Filter Topology
open Zeta23
open GaloisForLFunctions.HyperbolicArakelovTheory.CoupledOrbit

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The comb of the square degree points -/

/-- The rate of the jump `n² → m²` in the comb of the square degree points: the rate
`levyWeight (m²) (n²)` for the mass `1/m²`, rescaled to the mass `2/m` of `m²` in that comb. -/
def squareWeight (m n : ℕ) : ℝ := 2 * m * levyWeight (m ^ 2) (n ^ 2)

theorem squareWeight_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    squareWeight m n = 2 * n * jetKernel (m ^ 2) (n ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold squareWeight levyWeight
  rw [Nat.cast_pow, Nat.cast_pow, ← div_pow, Real.sqrt_sq (by positivity)]
  field_simp

/-- **The rates of the comb of squares are the Lévy density at the doubled displacement.** -/
theorem squareWeight_eq_archLevyDensity {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    squareWeight m n =
      2 / m * _root_.RHTower.archLevyDensity (2 * |Real.log ((m : ℝ) / n)|) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hne : m ^ 2 ≠ n ^ 2 := fun h => hmn (Nat.pow_left_injective two_ne_zero h)
  have hlog : |Real.log (((m ^ 2 : ℕ) : ℝ) / ((n ^ 2 : ℕ) : ℝ))| =
      2 * |Real.log ((m : ℝ) / n)| := by
    rw [Nat.cast_pow, Nat.cast_pow, ← div_pow, Real.log_pow, abs_mul]
    norm_num
  unfold squareWeight
  rw [levyWeight_eq_archLevyDensity (pow_pos hm 2) (pow_pos hn 2) hne, hlog, Nat.cast_pow]
  field_simp

/-- `1/(1 + t²)`, the density of the rates of the comb of squares beyond the jets. -/
def cauchyDensity (t : ℝ) : ℝ := 1 / (1 + t ^ 2)

theorem cauchyDensity_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    cauchyDensity y ≤ cauchyDensity x := by
  unfold cauchyDensity
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem squareWeight_of_lt {m n : ℕ} (hm : 0 < m) (h : m < n) :
    squareWeight m n = jetKernel m n + cauchyDensity ((m : ℝ) / n) / n := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hm.trans h
  have h' : (m : ℝ) < n := by exact_mod_cast h
  have hsq : (m : ℝ) ^ 2 < (n : ℝ) ^ 2 := by nlinarith
  rw [squareWeight_eq hm (hm.trans h), jetKernel, jetKernel, cauchyDensity, Nat.cast_pow,
    Nat.cast_pow, abs_of_neg (by linarith), abs_of_neg (by linarith), neg_sub, neg_sub]
  have h1 : (n : ℝ) - m ≠ 0 := (sub_pos.mpr h').ne'
  have h2 : (n : ℝ) ^ 2 - (m : ℝ) ^ 2 ≠ 0 := (sub_pos.mpr hsq).ne'
  field_simp
  ring

theorem squareWeight_of_gt {m n : ℕ} (hn : 0 < n) (h : n < m) :
    squareWeight m n =
      (1 / ((m : ℝ) - n) - 1 / ((m : ℝ) + n)) / 2 + cauchyDensity ((m : ℝ) / n) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hn.trans h
  have h' : (n : ℝ) < m := by exact_mod_cast h
  have hsq : (n : ℝ) ^ 2 < (m : ℝ) ^ 2 := by nlinarith
  rw [squareWeight_eq (hn.trans h) hn, jetKernel, cauchyDensity, Nat.cast_pow, Nat.cast_pow,
    abs_of_pos (by linarith)]
  have h1 : (m : ℝ) - n ≠ 0 := (sub_pos.mpr h').ne'
  have h2 : (m : ℝ) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := (sub_pos.mpr hsq).ne'
  field_simp
  ring

/-! ### The Riemann sums of `1/(1 + t²)` -/

theorem hasDerivAt_arctan_cauchyDensity (x : ℝ) :
    HasDerivAt Real.arctan (cauchyDensity x) x := Real.hasDerivAt_arctan x

/-- The Riemann sum below the degree point. -/
def cauchyLowSum (n : ℕ) : ℝ := ∑ m ∈ Ico 1 n, cauchyDensity ((m : ℝ) / n) / n

theorem cauchyLowSum_eq (n : ℕ) :
    cauchyLowSum n = ∑ k ∈ range (n - 1), cauchyDensity ((0 + (k : ℝ) + 1) / n) / n := by
  rw [cauchyLowSum, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ((1 + k : ℕ) : ℝ) = 0 + (k : ℝ) + 1 by push_cast; ring]

theorem cauchyLowSum_le {n : ℕ} (hn : 1 ≤ n) : cauchyLowSum n ≤ Real.pi / 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := sum_div_le_primitive Real.continuous_arctan.continuousOn
    (fun x _ => hasDerivAt_arctan_cauchyDensity x) (fun x y hx hxy => cauchyDensity_anti hx hxy)
    hn' le_rfl (n - 1)
  rw [← cauchyLowSum_eq, zero_div, Real.arctan_zero, sub_zero, zero_add] at h
  refine h.trans ?_
  rw [← Real.arctan_one]
  apply Real.arctan_strictMono.monotone
  rw [div_le_one hn']
  exact_mod_cast Nat.sub_le n 1

theorem le_cauchyLowSum {n : ℕ} (hn : 1 ≤ n) :
    Real.pi / 4 - Real.arctan (1 / n) ≤ cauchyLowSum n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := primitive_le_sum_div Real.continuous_arctan.continuousOn
    (fun x _ => hasDerivAt_arctan_cauchyDensity x) (fun x y hx hxy => cauchyDensity_anti hx hxy)
    hn' le_rfl (n - 1)
  rw [← cauchyLowSum_eq, zero_add, zero_add, Nat.cast_sub hn, Nat.cast_one, sub_add_cancel,
    div_self hn'.ne', Real.arctan_one] at h
  exact h

theorem tendsto_cauchyLowSum : Tendsto cauchyLowSum atTop (𝓝 (Real.pi / 4)) := by
  have h0 : Tendsto (fun n : ℕ => Real.arctan (1 / (n : ℝ))) atTop (𝓝 0) := by
    have h := (Real.continuous_arctan.tendsto 0).comp
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    rwa [Real.arctan_zero] at h
  have hlow : Tendsto (fun n : ℕ => Real.pi / 4 - Real.arctan (1 / (n : ℝ))) atTop
      (𝓝 (Real.pi / 4)) := by
    have h := (tendsto_const_nhds (x := Real.pi / 4) (f := (atTop : Filter ℕ))).sub h0
    rwa [sub_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn using le_cauchyLowSum hn
  · filter_upwards [eventually_ge_atTop 1] with n hn using cauchyLowSum_le hn

/-- The Riemann terms above the degree point. -/
def cauchyHighTerm (n j : ℕ) : ℝ := cauchyDensity (((n : ℝ) + j + 1) / n) / n

/-- The Riemann sum above the degree point. -/
def cauchyHighSum (n : ℕ) : ℝ := ∑' j : ℕ, cauchyHighTerm n j

theorem cauchyHighTerm_nonneg (n j : ℕ) : 0 ≤ cauchyHighTerm n j := by
  unfold cauchyHighTerm cauchyDensity
  positivity

theorem sum_cauchyHighTerm_le {n : ℕ} (hn : 1 ≤ n) (J : ℕ) :
    ∑ j ∈ range J, cauchyHighTerm n j ≤ Real.pi / 2 - Real.pi / 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := sum_div_le_primitive Real.continuous_arctan.continuousOn
    (fun x _ => hasDerivAt_arctan_cauchyDensity x) (fun x y hx hxy => cauchyDensity_anti hx hxy)
    hn' hn'.le J
  rw [div_self hn'.ne', Real.arctan_one] at h
  exact h.trans (sub_le_sub_right (Real.arctan_lt_pi_div_two _).le _)

theorem summable_cauchyHighTerm {n : ℕ} (hn : 1 ≤ n) : Summable (cauchyHighTerm n) :=
  summable_of_sum_range_le (cauchyHighTerm_nonneg n) (sum_cauchyHighTerm_le hn)

theorem cauchyHighSum_le {n : ℕ} (hn : 1 ≤ n) : cauchyHighSum n ≤ Real.pi / 2 - Real.pi / 4 :=
  Real.tsum_le_of_sum_range_le (cauchyHighTerm_nonneg n) (sum_cauchyHighTerm_le hn)

theorem le_cauchyHighSum {n : ℕ} (hn : 1 ≤ n) :
    Real.pi / 2 - Real.arctan (1 + 1 / n) ≤ cauchyHighSum n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hJ : Tendsto (fun J : ℕ => ((n : ℝ) + J + 1) / n) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_add_const_left _ (n : ℝ) tendsto_natCast_atTop_atTop)).atTop_div_const hn'
  have e : ((n : ℝ) + 1) / n = 1 + 1 / n := by field_simp
  have harc : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have hlim := (harc.comp hJ).sub_const (Real.arctan (1 + 1 / n))
  refine le_of_tendsto' hlim fun J => ?_
  have h := primitive_le_sum_div Real.continuous_arctan.continuousOn
    (fun x _ => hasDerivAt_arctan_cauchyDensity x) (fun x y hx hxy => cauchyDensity_anti hx hxy)
    hn' hn'.le J
  rw [e] at h
  exact h.trans ((summable_cauchyHighTerm hn).sum_le_tsum _ fun j _ => cauchyHighTerm_nonneg n j)

theorem tendsto_cauchyHighSum : Tendsto cauchyHighSum atTop (𝓝 (Real.pi / 4)) := by
  have hc : Tendsto (fun n : ℕ => Real.arctan (1 + 1 / (n : ℝ))) atTop (𝓝 (Real.pi / 4)) := by
    have h1 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [add_zero] at h
    have h := (Real.continuous_arctan.tendsto 1).comp h1
    rwa [Real.arctan_one] at h
  have hval : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
  have hlow : Tendsto (fun n : ℕ => Real.pi / 2 - Real.arctan (1 + 1 / (n : ℝ))) atTop
      (𝓝 (Real.pi / 4)) := by
    rw [← hval]
    exact tendsto_const_nhds.sub hc
  have hupp : Tendsto (fun _ : ℕ => Real.pi / 2 - Real.pi / 4) atTop (𝓝 (Real.pi / 4)) := by
    rw [hval]
    exact tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn using le_cauchyHighSum hn
  · filter_upwards [eventually_ge_atTop 1] with n hn using cauchyHighSum_le hn

/-! ### The total rate of the comb of squares -/

theorem squareWeight_add_succ {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    squareWeight (n + j + 1) n = teleTerm n j + cauchyHighTerm n j := by
  have e1 : ((n + j + 1 : ℕ) : ℝ) - n = j + 1 := by push_cast; ring
  have e2 : ((n + j + 1 : ℕ) : ℝ) + n = ((2 * n : ℕ) : ℝ) + j + 1 := by push_cast; ring
  have e3 : ((n + j + 1 : ℕ) : ℝ) = (n : ℝ) + j + 1 := by push_cast; ring
  rw [squareWeight_of_gt hn (by omega), e1, e2, e3, teleTerm, cauchyHighTerm]

theorem hasSum_squareWeight_above {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun j : ℕ => squareWeight (n + j + 1) n) (harm (2 * n) / 2 + cauchyHighSum n) := by
  have hfun : (fun j : ℕ => squareWeight (n + j + 1) n) =
      fun j => teleTerm n j + cauchyHighTerm n j := funext (squareWeight_add_succ hn)
  rw [hfun]
  exact (hasSum_teleTerm n).add (summable_cauchyHighTerm hn).hasSum

/-- The total rate of the jumps out of `n²` in the comb of the square degree points. -/
def squareRow (n : ℕ) : ℝ :=
  ∑ m ∈ Ico 1 n, squareWeight m n + ∑' j : ℕ, squareWeight (n + j + 1) n

theorem squareRow_eq {n : ℕ} (hn : 1 ≤ n) :
    squareRow n = harm (2 * n) - 3 / (4 * (n : ℝ)) + cauchyLowSum n + cauchyHighSum n := by
  have hlow : ∑ m ∈ Ico 1 n, squareWeight m n =
      harm (2 * n) / 2 - 3 / (4 * (n : ℝ)) + cauchyLowSum n := by
    have h := sum_jetKernel_row hn le_rfl
    rw [Finset.Ioc_self, Finset.sum_empty, add_zero, Nat.sub_self, harm_zero, zero_add,
      ← two_mul] at h
    rw [Finset.sum_congr rfl fun m hm =>
      squareWeight_of_lt (Finset.mem_Ico.mp hm).1 (Finset.mem_Ico.mp hm).2,
      Finset.sum_add_distrib, h, cauchyLowSum]
  rw [squareRow, hlow, (hasSum_squareWeight_above hn).tsum_eq]
  ring

/-- **The counterterm of the comb of squares**: the total rate out of `n²` minus `log(n/4π)`
tends to `−A(0)`; the density of the comb at `n²` is `n/2`. -/
theorem tendsto_squareRow_sub_log :
    Tendsto (fun n : ℕ => squareRow n - Real.log ((n : ℝ) / (4 * Real.pi))) atTop
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
  have hlim := (((hH.add_const (Real.log 2 + Real.log (4 * Real.pi))).sub h3).add
    tendsto_cauchyLowSum).add tendsto_cauchyHighSum
  have h8 : Real.log (8 * Real.pi) = Real.log 2 + Real.log (4 * Real.pi) := by
    rw [show (8 : ℝ) * Real.pi = 2 * (4 * Real.pi) by ring,
      Real.log_mul (x := 2) (y := 4 * Real.pi) (by norm_num) (by positivity)]
  have hval : Real.eulerMascheroniConstant + (Real.log 2 + Real.log (4 * Real.pi)) - 0 +
      Real.pi / 4 + Real.pi / 4 =
      Real.eulerMascheroniConstant + Real.pi / 2 + Real.log (8 * Real.pi) := by
    rw [h8]
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply]
  rw [squareRow_eq hn, Real.log_div hn'.ne' (by positivity),
    show ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) by push_cast; ring,
    Real.log_mul (x := 2) (y := (n : ℝ)) (by norm_num) hn'.ne']
  ring

/-! ### The rows of the carrier -/

/-- The term of the carrier at the displacement `a/n` is the jet pairing of the square
degrees. -/
theorem jetKernel_sq_sq {a n : ℕ} (ha : 0 < a) (h : a < n) :
    jetKernel (a ^ 2) (n ^ 2) = ((n : ℝ) ^ 2)⁻¹ * (1 / (1 - ((a : ℝ) / n) ^ 4)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast ha.trans h
  have h' : (a : ℝ) < n := by exact_mod_cast h
  have hsq : (a : ℝ) ^ 2 < (n : ℝ) ^ 2 := by nlinarith
  rw [jetKernel, Nat.cast_pow, Nat.cast_pow, abs_of_neg (by linarith), neg_sub]
  have h1 : (n : ℝ) ^ 2 - (a : ℝ) ^ 2 ≠ 0 := (sub_pos.mpr hsq).ne'
  have h2 : 1 - ((a : ℝ) / n) ^ 4 =
      ((n : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((n : ℝ) ^ 2 + (a : ℝ) ^ 2) / (n : ℝ) ^ 4 := by
    field_simp
    ring
  rw [h2]
  field_simp
  ring

/-- **The rows of the carrier are the primitive jets of the square degree points.** -/
theorem geometricRow_eq_sum_jetKernel {n : ℕ} (hn : 2 ≤ n) :
    geometricRow n =
      ∑ a ∈ Icc 1 n, if Nat.Coprime n a then jetKernel (a ^ 2) (n ^ 2) else 0 := by
  rw [geometricRow, if_pos hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  by_cases hc : Nat.Coprime n a
  · have hlt : a < n := by
      rcases Nat.lt_or_ge a n with h | h
      · exact h
      · have hEq : a = n := le_antisymm (mem_Icc.mp ha).2 h
        rw [hEq, Nat.coprime_self] at hc
        omega
    rw [if_pos hc, if_pos hc, jetKernel_sq_sq (mem_Icc.mp ha).1 hlt]
  · rw [if_neg hc, if_neg hc, mul_zero]

/-- **Half a row of the carrier**: the rates into the points below `n²` are the collision term
`½H_{n−1}` plus `2/n` times the smooth row without its endpoint. -/
theorem sum_squareWeight_below {n : ℕ} (hn : 1 ≤ n) :
    ∑ m ∈ Ico 1 n, squareWeight m n = harm (n - 1) / 2 + 2 / n * (smoothRow n - 3 / 8) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ m ∈ Ico 1 n, squareWeight m n =
      1 / 2 * (1 / ((n : ℝ) - m)) + 2 / n * regularProfile ((m : ℝ) / n) := by
    intro m hm
    have hm1 := (mem_Ico.mp hm).1
    have hmn := (mem_Ico.mp hm).2
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm1
    have h' : (m : ℝ) < n := by exact_mod_cast hmn
    rw [squareWeight_eq hm1 hn, jetKernel_sq_sq hm1 hmn,
      profile_split (div_nonneg hm'.le hn'.le) ((div_lt_one hn').mpr h')]
    have h1 : (n : ℝ) - m ≠ 0 := (sub_pos.mpr h').ne'
    have h2 : (1 : ℝ) - (m : ℝ) / n = ((n : ℝ) - m) / n := by field_simp
    rw [h2]
    field_simp
    ring
  have hend : regularProfile 1 = 3 / 8 := by norm_num [regularProfile]
  have hsmooth : ∑ m ∈ Ico 1 n, regularProfile ((m : ℝ) / n) = smoothRow n - 3 / 8 := by
    have hI : Icc 1 n = insert n (Ico 1 n) := by
      ext k
      simp only [mem_Icc, mem_insert, mem_Ico]
      omega
    rw [smoothRow, hI, Finset.sum_insert (by simp), div_self hn'.ne', hend]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_Ico_inv_sub, hsmooth]
  ring

/-- Half a row of the carrier is its collision term plus its density term up to `9/(4n)`. -/
theorem abs_sum_squareWeight_below_sub_le {n : ℕ} (hn : 1 ≤ n) :
    |∑ m ∈ Ico 1 n, squareWeight m n - (harm (n - 1) / 2 + 2 * regularMean)| ≤
      9 / (4 * (n : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have herr := abs_rowError_le n
  have e : harm (n - 1) / 2 + 2 / n * (smoothRow n - 3 / 8) -
      (harm (n - 1) / 2 + 2 * regularMean) = 2 / n * (rowError n - 3 / 8) := by
    unfold rowError
    field_simp
    ring
  have h1 : |rowError n - 3 / 8| ≤ 9 / 8 := by
    rw [abs_le] at herr ⊢
    constructor <;> linarith [herr.1, herr.2]
  rw [sum_squareWeight_below hn, e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / n)]
  calc 2 / (n : ℝ) * |rowError n - 3 / 8| ≤ 2 / n * (9 / 8) := by gcongr
    _ = 9 / (4 * (n : ℝ)) := by
        field_simp
        ring

/-! ### The two counterterms -/

theorem harm_eq_harm_pred_add {n : ℕ} (hn : 1 ≤ n) : harm n = harm (n - 1) + 1 / (n : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [harm_succ, Nat.add_sub_cancel]
  push_cast
  rfl

/-- **The two counterterms of the carrier are the mesh and Weil's constant**: symmetrized, the
collision term and the density term are `H_{n−1} + 4c₀`, and
`H_{n−1} + 4c₀ − (log(n/4π) − A(0)) → 0`. -/
theorem tendsto_counterterms_sub :
    Tendsto (fun n : ℕ => harm (n - 1) + 4 * regularMean -
      (Real.log ((n : ℝ) / (4 * Real.pi)) - EF.gammaBracket 0)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have h8 : Real.log (8 * Real.pi) = Real.log 2 + Real.log (4 * Real.pi) := by
    rw [show (8 : ℝ) * Real.pi = 2 * (4 * Real.pi) by ring,
      Real.log_mul (x := 2) (y := 4 * Real.pi) (by norm_num) (by positivity)]
  have hz : Real.eulerMascheroniConstant - 0 +
      (4 * regularMean + Real.log (4 * Real.pi) + EF.gammaBracket 0) = 0 := by
    rw [regularMean_eq, _root_.RHTower.ArchimedeanAnomaly.gammaBracket_zero_eq, h8]
    ring
  have hlim := (tendsto_harm_sub_log.sub h1).add_const
    (4 * regularMean + Real.log (4 * Real.pi) + EF.gammaBracket 0)
  rw [hz] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [harm_eq_harm_pred_add hn, Real.log_div hn'.ne' (by positivity)]
  ring

/-- **The subtraction of the carrier removes Weil's constant**: the total rate of the comb of
squares at `n²` minus the symmetrized counterterms `H_{n−1} + 4c₀` tends to `0`. -/
theorem tendsto_squareRow_sub_counterterms :
    Tendsto (fun n : ℕ => squareRow n - (harm (n - 1) + 4 * regularMean)) atTop (𝓝 0) := by
  have h := (tendsto_squareRow_sub_log.add_const (EF.gammaBracket 0)).sub tendsto_counterterms_sub
  rw [neg_add_cancel, sub_zero] at h
  refine h.congr fun n => ?_
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
