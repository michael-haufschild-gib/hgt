import GaloisForLFunctions.HTGeometry.CircleQuadratureAnnihilatingMeasure

/-!
# Sector-positive Wolff measures with rapidly decaying weights

There is a discrete measure `Σ_i c_i δ_{x_i}` with pairwise distinct nodes in `5/4 ≤ |x| ≤ 10`, a
unit mass at the isolated node `x = 5/4`, and weights in the sector `|c_i| ≤ 2 Re c_i` whose
arguments tend to `0`. It has `Σ_i |c_i|^p < ∞` for every `p > 0`, and `Σ_i c_i x_i^m = 0` for
every `m ≥ 1` (`exists_sector_wolff_measure`).

**Construction.** This is the circle quadrature of `CircleQuadratureAnnihilatingMeasure`, with the
discrete Fourier sum taken over `1 ≤ i < N_k` only and a real shift `κ_k L_k`, `κ_k = 2^k + 3`,
added to every weight of stage `k`:
`w_{k,j} = κ_k L_k − N_k^{−1} Σ_{1≤i<N_k} E_k(i) (R_k ω_k^j)^{−i}`.
* The shift contributes `κ_k L_k R_k^m Σ_j ω_k^{jm} = 0` to the moments `1 ≤ m < N_k`, so the
  moments `1 ≤ m < N_k` are still killed exactly (`sum_sWeight_mul_node_pow`).
* The oscillating part has modulus at most `L_k`, so `Re w ≥ (κ_k − 1)L_k`, `|Im w| ≤ L_k` and
  `|w| ≤ (κ_k + 1) L_k ≤ 2 Re w` (`sWeight_sector`).
* The bound recursion becomes `L_{k+1} = (N_k(κ_k + 1) + 1) 2^{−4^{k+4}} L_k`, which still decays
  super-exponentially.

So neither positivity of the real parts, nor a fixed sector, nor arguments tending to `0`, together
with any power-type summability of the weights, prevents the moments `m ≥ 1` of a discrete measure
on an annulus from vanishing identically. The node series `Σ_i c_i/(1 − t x_i)` equals the constant
`Σ_i c_i` on `|t| < 1/10` (`tsum_sCoef_div_eq_tsum`), yet it has a simple pole at `t = 4/5`
(`norm_tsum_sCoef_div_ge`).
-/

open Complex Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.CircleQuadratureSector

open CircleQuadratureAnnihilating

noncomputable section

/-! ## Stage data -/

/-- The shift multiplier `κ_k = 2^k + 3`. -/
def shift (k : ℕ) : ℝ := 2 ^ k + 3

/-- Bounds `L_0 = 1`, `L_{k+1} = (N_k(κ_k + 1) + 1) L_k / 2^{a_k}`. -/
def sBound : ℕ → ℝ
  | 0 => 1
  | k + 1 => ((nodeCount k : ℝ) * (shift k + 1) + 1) * sBound k / 2 ^ gainExp k

/-- Residual moments of the shifted quadrature. -/
def sResidual : ℕ → ℕ → ℂ
  | 0, m => (5 / 4 : ℂ) ^ m
  | k + 1, m => sResidual k m + ∑ j ∈ range (nodeCount k),
      (((shift k * sBound k : ℝ) : ℂ) - (1 / (nodeCount k : ℂ)) *
        ∑ i ∈ Ico 1 (nodeCount k), sResidual k i / node k j ^ i) * node k j ^ m

/-- The oscillating part of the stage weights. -/
def osc (k j : ℕ) : ℂ :=
  (1 / (nodeCount k : ℂ)) * ∑ i ∈ Ico 1 (nodeCount k), sResidual k i / node k j ^ i

/-- The stage weights `κ_k L_k − osc`. -/
def sWeight (k j : ℕ) : ℂ := ((shift k * sBound k : ℝ) : ℂ) - osc k j

theorem sResidual_succ (k m : ℕ) :
    sResidual (k + 1) m = sResidual k m + ∑ j ∈ range (nodeCount k), sWeight k j * node k j ^ m :=
  rfl

theorem shift_pos (k : ℕ) : 0 < shift k := by unfold shift; positivity

theorem sBound_nonneg : ∀ k, 0 ≤ sBound k
  | 0 => by norm_num [sBound]
  | k + 1 => by
    show 0 ≤ ((nodeCount k : ℝ) * (shift k + 1) + 1) * sBound k / 2 ^ gainExp k
    have := sBound_nonneg k
    have := shift_pos k
    positivity

/-! ## Exactness -/

theorem sum_node_pow (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    ∑ j ∈ range (nodeCount k), node k j ^ m = 0 := by
  have hζ := isPrimitiveRoot_root k
  have hterm : ∀ j, node k j ^ m = (radius k : ℂ) ^ m * (root k ^ m) ^ j := by
    intro j; unfold node; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j m]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]
  have hζ1 : root k ^ m ≠ 1 := by
    intro h
    have := hζ.pow_inj hm (nodeCount_pos k) (by rw [h, pow_zero])
    omega
  have hζN : (root k ^ m) ^ nodeCount k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [geom_sum_eq hζ1, hζN, sub_self, zero_div, mul_zero]

/-- **The shifted quadrature still kills the moments `1 ≤ m < N_k`.** -/
theorem sum_sWeight_mul_node_pow (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    ∑ j ∈ range (nodeCount k), sWeight k j * node k j ^ m = -sResidual k m := by
  have hN : (nodeCount k : ℂ) ≠ 0 := by exact_mod_cast (nodeCount_pos k).ne'
  have hsplit : ∑ j ∈ range (nodeCount k), sWeight k j * node k j ^ m =
      ((shift k * sBound k : ℝ) : ℂ) * ∑ j ∈ range (nodeCount k), node k j ^ m -
        ∑ j ∈ range (nodeCount k), osc k j * node k j ^ m := by
    unfold sWeight
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hosc : ∑ j ∈ range (nodeCount k), osc k j * node k j ^ m =
      (1 / (nodeCount k : ℂ)) * ∑ i ∈ Ico 1 (nodeCount k),
        sResidual k i * ∑ j ∈ range (nodeCount k), node k j ^ m / node k j ^ i := by
    calc ∑ j ∈ range (nodeCount k), osc k j * node k j ^ m
        = ∑ j ∈ range (nodeCount k), ∑ i ∈ Ico 1 (nodeCount k),
            (1 / (nodeCount k : ℂ)) * (sResidual k i * (node k j ^ m / node k j ^ i)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          unfold osc
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ i ∈ Ico 1 (nodeCount k), ∑ j ∈ range (nodeCount k),
            (1 / (nodeCount k : ℂ)) * (sResidual k i * (node k j ^ m / node k j ^ i)) :=
          Finset.sum_comm
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit, sum_node_pow k h1 hm, mul_zero, zero_sub, hosc]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [sum_node_pow_div k hm (Finset.mem_Ico.mp hi).2])]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_Ico.mpr ⟨h1, hm⟩)]
  field_simp

theorem sResidual_succ_eq_zero (k : ℕ) {m : ℕ} (h1 : 1 ≤ m) (hm : m < nodeCount k) :
    sResidual (k + 1) m = 0 := by
  rw [sResidual_succ, sum_sWeight_mul_node_pow k h1 hm, add_neg_cancel]

/-! ## Bounds and the sector -/

theorem norm_osc_le {k : ℕ} (h : ∀ m, 1 ≤ m → ‖sResidual k m‖ ≤ sBound k * radius k ^ m)
    (j : ℕ) : ‖osc k j‖ ≤ sBound k := by
  have hN : (0 : ℝ) < nodeCount k := by exact_mod_cast nodeCount_pos k
  unfold osc
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hsum : ‖∑ i ∈ Ico 1 (nodeCount k), sResidual k i / node k j ^ i‖ ≤
      (nodeCount k : ℝ) * sBound k := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Ico 1 (nodeCount k), ‖sResidual k i / node k j ^ i‖ ≤ sBound k := by
      intro i hi
      rw [norm_div, norm_pow, norm_node, div_le_iff₀ (pow_pos (radius_pos k) _)]
      exact h i (Finset.mem_Ico.mp hi).1
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [Nat.card_Ico, nsmul_eq_mul]
    have : ((nodeCount k - 1 : ℕ) : ℝ) ≤ nodeCount k := by exact_mod_cast Nat.sub_le _ _
    exact mul_le_mul_of_nonneg_right this (sBound_nonneg k)
  calc 1 / (nodeCount k : ℝ) * ‖∑ i ∈ Ico 1 (nodeCount k), sResidual k i / node k j ^ i‖
      ≤ 1 / (nodeCount k : ℝ) * ((nodeCount k : ℝ) * sBound k) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = sBound k := by field_simp

theorem sWeight_re_ge {k : ℕ} (h : ∀ m, 1 ≤ m → ‖sResidual k m‖ ≤ sBound k * radius k ^ m)
    (j : ℕ) : (shift k - 1) * sBound k ≤ (sWeight k j).re := by
  have ho := norm_osc_le h j
  have hre : (osc k j).re ≤ ‖osc k j‖ := Complex.re_le_norm _
  unfold sWeight
  rw [Complex.sub_re, Complex.ofReal_re]
  linarith

theorem abs_sWeight_im_le {k : ℕ} (h : ∀ m, 1 ≤ m → ‖sResidual k m‖ ≤ sBound k * radius k ^ m)
    (j : ℕ) : |(sWeight k j).im| ≤ sBound k := by
  unfold sWeight
  rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg]
  exact (Complex.abs_im_le_norm _).trans (norm_osc_le h j)

theorem norm_sWeight_le {k : ℕ} (h : ∀ m, 1 ≤ m → ‖sResidual k m‖ ≤ sBound k * radius k ^ m)
    (j : ℕ) : ‖sWeight k j‖ ≤ (shift k + 1) * sBound k := by
  unfold sWeight
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (shift_pos k).le
    (sBound_nonneg k))]
  have := norm_osc_le h j
  linarith

/-- **The residual moments `m ≥ 1` are controlled at every stage.** -/
theorem norm_sResidual_le : ∀ k m, 1 ≤ m → ‖sResidual k m‖ ≤ sBound k * radius k ^ m
  | 0, m, _ => by
    show ‖(5 / 4 : ℂ) ^ m‖ ≤ 1 * (4 / 3 : ℝ) ^ m
    rw [norm_pow, one_mul, norm_five_fourths]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
  | k + 1, m, h1 => by
    have ih := norm_sResidual_le k
    by_cases hm : m < nodeCount k
    · rw [sResidual_succ_eq_zero k h1 hm, norm_zero]
      exact mul_nonneg (sBound_nonneg _) (pow_nonneg (radius_pos _).le _)
    · push Not at hm
      have hw := norm_sWeight_le ih
      have hR0 : 0 ≤ radius k ^ m := pow_nonneg (radius_pos k).le _
      have hsum : ‖∑ j ∈ range (nodeCount k), sWeight k j * node k j ^ m‖ ≤
          (nodeCount k : ℝ) * ((shift k + 1) * sBound k * radius k ^ m) := by
        refine (norm_sum_le _ _).trans ?_
        have hterm : ∀ j ∈ range (nodeCount k), ‖sWeight k j * node k j ^ m‖ ≤
            (shift k + 1) * sBound k * radius k ^ m := by
          intro j _
          rw [norm_mul, norm_pow, norm_node]
          exact mul_le_mul_of_nonneg_right (hw j) hR0
        refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
        rw [Finset.card_range, nsmul_eq_mul]
      have hgain := two_pow_mul_radius_pow_le hm
      have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
      have hL0 := sBound_nonneg k
      have hs := shift_pos k
      calc ‖sResidual (k + 1) m‖
          ≤ ‖sResidual k m‖ + ‖∑ j ∈ range (nodeCount k), sWeight k j * node k j ^ m‖ := by
            rw [sResidual_succ]; exact norm_add_le _ _
        _ ≤ sBound k * radius k ^ m +
              (nodeCount k : ℝ) * ((shift k + 1) * sBound k * radius k ^ m) :=
            add_le_add (ih m h1) hsum
        _ = ((nodeCount k : ℝ) * (shift k + 1) + 1) * sBound k / 2 ^ gainExp k *
              (2 ^ gainExp k * radius k ^ m) := by field_simp; ring
        _ ≤ ((nodeCount k : ℝ) * (shift k + 1) + 1) * sBound k / 2 ^ gainExp k *
              radius (k + 1) ^ m :=
            mul_le_mul_of_nonneg_left hgain (by positivity)
        _ = sBound (k + 1) * radius (k + 1) ^ m := rfl

/-- **Sector.** `(κ_k − 1)|Im w| ≤ Re w` and `|w| ≤ 2 Re w`. -/
theorem sWeight_sector (k j : ℕ) :
    (shift k - 1) * |(sWeight k j).im| ≤ (sWeight k j).re ∧
      ‖sWeight k j‖ ≤ 2 * (sWeight k j).re := by
  have h := norm_sResidual_le k
  have hre := sWeight_re_ge h j
  have him := abs_sWeight_im_le h j
  have hn := norm_sWeight_le h j
  have hL := sBound_nonneg k
  have hs : 2 ≤ shift k - 1 := by
    unfold shift; have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num); linarith
  constructor
  · nlinarith
  · nlinarith

/-! ## Explicit decay -/

theorem quadratic_le_four_pow' (k : ℕ) : 3 * k ^ 2 + 21 * k + 27 ≤ 4 ^ (k + 4) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by ring, pow_succ (4 : ℕ) (k + 4)]
    nlinarith

theorem stage_factor_le (k : ℕ) :
    (nodeCount k : ℝ) * (shift k + 1) + 1 ≤ 2 ^ (4 * k + 12) := by
  unfold nodeCount shift
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ 2 ^ (3 * k + 8) := one_le_pow₀ (by norm_num)
  have e : (2 : ℝ) ^ (4 * k + 12) = 2 ^ (3 * k + 8) * 2 ^ k * 16 := by
    rw [← pow_add, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_add]
    congr 1; ring
  push_cast
  rw [e]
  nlinarith

theorem sBound_le_one : ∀ k, sBound k ≤ 1
  | 0 => by norm_num [sBound]
  | k + 1 => by
    show ((nodeCount k : ℝ) * (shift k + 1) + 1) * sBound k / 2 ^ gainExp k ≤ 1
    have hb := sBound_le_one k
    have hb0 := sBound_nonneg k
    have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
    rw [div_le_one h2]
    have hexp : 4 * k + 12 ≤ gainExp k := by
      have := quadratic_le_four_pow' k; unfold gainExp; nlinarith
    have hpow : (2 : ℝ) ^ (4 * k + 12) ≤ 2 ^ gainExp k := pow_le_pow_right₀ (by norm_num) hexp
    have := stage_factor_le k
    have hf0 : 0 ≤ (nodeCount k : ℝ) * (shift k + 1) + 1 := by
      have := shift_pos k; positivity
    calc ((nodeCount k : ℝ) * (shift k + 1) + 1) * sBound k
        ≤ ((nodeCount k : ℝ) * (shift k + 1) + 1) * 1 := mul_le_mul_of_nonneg_left hb hf0
      _ ≤ 2 ^ gainExp k := by linarith

/-- `L_{k+1} ≤ 2^{−((3k+11)(k+1) + 3k + 4)}`. -/
theorem sBound_succ_le (k : ℕ) :
    sBound (k + 1) ≤ (1 / 2 : ℝ) ^ ((3 * k + 11) * (k + 1) + 3 * k + 4) := by
  show ((nodeCount k : ℝ) * (shift k + 1) + 1) * sBound k / 2 ^ gainExp k ≤ _
  set E := (3 * k + 11) * (k + 1) + 3 * k + 4 with hE
  have hexp : E + (4 * k + 12) ≤ gainExp k := by
    have := quadratic_le_four_pow' k; unfold gainExp; rw [hE]; nlinarith
  have hb := sBound_le_one k
  have hb0 := sBound_nonneg k
  have h2 : (0 : ℝ) < 2 ^ gainExp k := by positivity
  rw [div_le_iff₀ h2, one_div_pow]
  have hpow : (2 : ℝ) ^ (E + (4 * k + 12)) ≤ 2 ^ gainExp k :=
    pow_le_pow_right₀ (by norm_num) hexp
  rw [pow_add] at hpow
  have h2E : (0 : ℝ) < 2 ^ E := by positivity
  have := stage_factor_le k
  have hf0 : 0 ≤ (nodeCount k : ℝ) * (shift k + 1) + 1 := by
    have := shift_pos k; positivity
  calc ((nodeCount k : ℝ) * (shift k + 1) + 1) * sBound k ≤ 2 ^ (4 * k + 12) := by nlinarith
    _ = 1 / 2 ^ E * (2 ^ E * 2 ^ (4 * k + 12)) := by field_simp
    _ ≤ 1 / 2 ^ E * 2 ^ gainExp k := mul_le_mul_of_nonneg_left hpow (by positivity)

/-! ## The configuration -/

/-- The weights of the shifted configuration. -/
def sCoef : Idx → ℂ
  | ⟨0, _⟩ => 1
  | ⟨k + 1, j⟩ => sWeight k j

theorem sCoef_sector (i : Idx) : ‖sCoef i‖ ≤ 2 * (sCoef i).re := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero => show ‖(1 : ℂ)‖ ≤ 2 * (1 : ℂ).re; simp
  | succ k => exact (sWeight_sector k j).2

theorem finite_sCoef_arg {ε : ℝ} (hε : 0 < ε) :
    {i : Idx | ε * (sCoef i).re < |(sCoef i).im|}.Finite := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 / ε < 2 ^ K := pow_unbounded_of_one_lt _ (by norm_num)
  refine (((Finset.range (K + 1)).sigma fun k =>
    (Finset.univ : Finset (Fin (count k)))).finite_toSet).subset fun i hi => ?_
  obtain ⟨k, j⟩ := i
  simp only [Set.mem_setOf_eq] at hi
  simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio, Finset.coe_univ,
    Set.mem_univ, and_true]
  by_contra hk
  push Not at hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hsec := (sWeight_sector k' j).1
  have hpow : (2 : ℝ) ^ K ≤ 2 ^ k' := pow_le_pow_right₀ (by norm_num) (by omega)
  have hs : 1 / ε < shift k' - 1 := by unfold shift; linarith
  have hre0 : 0 ≤ (sWeight k' j).re := by
    have := abs_nonneg (sWeight k' j).im
    have h2 : 0 < shift k' - 1 := lt_trans (by positivity) hs
    nlinarith
  have hi' : ε * (sWeight k' j).re < |(sWeight k' j).im| := hi
  have h1 : (shift k' - 1) * |(sWeight k' j).im| ≤ (sWeight k' j).re := hsec
  have h3 : 1 < ε * (shift k' - 1) := by
    rw [div_lt_iff₀ hε] at hs; linarith
  nlinarith [abs_nonneg (sWeight k' j).im]

theorem norm_sCoef_le (i : Idx) : ‖sCoef i‖ ≤ 2 ^ (i.1 + 3) := by
  obtain ⟨k, j⟩ := i
  cases k with
  | zero => show ‖(1 : ℂ)‖ ≤ 2 ^ 3; norm_num
  | succ k =>
    show ‖sWeight k j‖ ≤ 2 ^ (k + 1 + 3)
    refine (norm_sWeight_le (norm_sResidual_le k) j).trans ?_
    have hL := sBound_le_one k
    have hL0 := sBound_nonneg k
    have hs : shift k + 1 ≤ 2 ^ (k + 1 + 3) := by
      unfold shift
      have : (2 : ℝ) ^ (k + 1 + 3) = 2 ^ k * 16 := by
        rw [show k + 1 + 3 = k + 4 by ring, pow_add]; norm_num
      rw [this]
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      linarith
    nlinarith [shift_pos k]

theorem summable_sStage_rpow {p : ℝ} (hp : 0 < p) :
    Summable fun k : ℕ => (nodeCount (k + 1) : ℝ) * ((shift (k + 1) + 1) * sBound (k + 1)) ^ p := by
  have hq0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * p) := by positivity
  have hq1 : (1 / 2 : ℝ) ^ (2 * p) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  refine Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hq0 hq1) ?_
  filter_upwards [eventually_ge_atTop ⌈1 / p⌉₊] with k hk
  have hkp : 1 ≤ p * ((k : ℝ) + 1) := by
    have h1 : 1 / p ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have h2 : 1 / p * p = 1 := by field_simp
    nlinarith
  have hb0 := sBound_nonneg (k + 1)
  set E : ℕ := (3 * k + 11) * (k + 1) + 3 * k + 4 with hE
  have hbE := sBound_succ_le k
  have hsh : shift (k + 1) + 1 ≤ (2 : ℝ) ^ ((k + 4 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; unfold shift
    have : (2 : ℝ) ^ (k + 4) = 2 ^ (k + 1) * 8 := by
      rw [show k + 4 = (k + 1) + 3 by ring, pow_add]; norm_num
    rw [this]
    have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
    linarith
  have hsh0 : 0 ≤ shift (k + 1) + 1 := by have := shift_pos (k + 1); linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hprod : (shift (k + 1) + 1) * sBound (k + 1) ≤
      (2 : ℝ) ^ ((k + 4 : ℕ) : ℝ) * (2 : ℝ) ^ (-(E : ℝ)) := by
    have : (1 / 2 : ℝ) ^ E = (2 : ℝ) ^ (-(E : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
    rw [← this]
    exact mul_le_mul hsh hbE hb0 (by positivity)
  have h1 : ((shift (k + 1) + 1) * sBound (k + 1)) ^ p ≤
      ((2 : ℝ) ^ ((k + 4 : ℕ) : ℝ) * (2 : ℝ) ^ (-(E : ℝ))) ^ p :=
    Real.rpow_le_rpow (mul_nonneg hsh0 hb0) hprod hp.le
  have h2 : ((2 : ℝ) ^ ((k + 4 : ℕ) : ℝ) * (2 : ℝ) ^ (-(E : ℝ))) ^ p =
      (2 : ℝ) ^ ((((k + 4 : ℕ) : ℝ) + -(E : ℝ)) * p) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_mul (by norm_num)]
  have h3 : (nodeCount (k + 1) : ℝ) = (2 : ℝ) ^ ((3 * k + 11 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; unfold nodeCount; push_cast; ring_nf
  have h4 : ((1 / 2 : ℝ) ^ (2 * p)) ^ k = (2 : ℝ) ^ (-(2 * p * k)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num)]
  rw [h4]
  calc (nodeCount (k + 1) : ℝ) * ((shift (k + 1) + 1) * sBound (k + 1)) ^ p
      ≤ (nodeCount (k + 1) : ℝ) * (2 : ℝ) ^ ((((k + 4 : ℕ) : ℝ) + -(E : ℝ)) * p) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (2 : ℝ) ^ (((3 * k + 11 : ℕ) : ℝ) + (((k + 4 : ℕ) : ℝ) + -(E : ℝ)) * p) := by
        rw [h3, ← Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ (-(2 * p * k)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hE]
        push_cast
        nlinarith

theorem summable_norm_sCoef_rpow {p : ℝ} (hp : 0 < p) :
    Summable fun i : Idx => ‖sCoef i‖ ^ p := by
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  refine ⟨fun k => Summable.of_finite, ?_⟩
  rw [← summable_nat_add_iff 1]
  have hstage : ∀ k : ℕ, ∑' j : Fin (count (k + 1)), ‖sCoef ⟨k + 1, j⟩‖ ^ p ≤
      (nodeCount k : ℝ) * ((shift k + 1) * sBound k) ^ p := by
    intro k
    rw [tsum_fintype]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (nodeCount k))),
        ‖sWeight k j‖ ^ p ≤ ((shift k + 1) * sBound k) ^ p := fun j _ =>
      Real.rpow_le_rpow (norm_nonneg _) (norm_sWeight_le (norm_sResidual_le k) j) hp.le
    have := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => by positivity) hstage ?_
  rw [← summable_nat_add_iff 1]
  exact summable_sStage_rpow hp

theorem summable_norm_sCoef : Summable fun i : Idx => ‖sCoef i‖ := by
  simpa using summable_norm_sCoef_rpow (p := 1) one_pos

/-! ## Vanishing moments `m ≥ 1` -/

/-- The moment contribution of stage `k`. -/
def sStageSum (m k : ℕ) : ℂ := ∑ j : Fin (count k), sCoef ⟨k, j⟩ * point ⟨k, j⟩ ^ m

theorem sStageSum_succ (m k : ℕ) : sStageSum m (k + 1) = sResidual (k + 1) m - sResidual k m := by
  unfold sStageSum
  rw [sResidual_succ, add_sub_cancel_left]
  exact Fin.sum_univ_eq_sum_range (fun j => sWeight k j * node k j ^ m) (nodeCount k)

theorem sum_range_sStageSum (m K : ℕ) : ∑ k ∈ range (K + 1), sStageSum m k = sResidual K m := by
  induction K with
  | zero => simp [sStageSum, count, sCoef, point, sResidual]
  | succ K ih => rw [Finset.sum_range_succ, ih, sStageSum_succ]; ring

theorem sResidual_eq_zero_of_le {m k : ℕ} (h1 : 1 ≤ m) (hk : m ≤ k) : sResidual (k + 1) m = 0 := by
  apply sResidual_succ_eq_zero k h1
  unfold nodeCount
  calc m ≤ k := hk
    _ < 2 ^ k := Nat.lt_two_pow_self
    _ ≤ 2 ^ (3 * k + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem hasSum_sStageSum {m : ℕ} (h1 : 1 ≤ m) : HasSum (sStageSum m) 0 := by
  have hzero : ∀ k ∉ range (m + 2), sStageSum m k = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [sStageSum_succ, sResidual_eq_zero_of_le h1 (by omega)]
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    rw [sResidual_eq_zero_of_le h1 (by omega), sub_zero]
  have h : HasSum (sStageSum m) (∑ b ∈ range (m + 2), sStageSum m b) :=
    hasSum_sum_of_ne_finset_zero hzero
  rwa [sum_range_sStageSum, sResidual_eq_zero_of_le h1 le_rfl] at h

theorem summable_sCoef_mul_point_pow (m : ℕ) : Summable fun i : Idx => sCoef i * point i ^ m := by
  refine Summable.of_norm_bounded (summable_norm_sCoef.mul_right ((10 : ℝ) ^ m)) fun i => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_point_le i) m)
    (norm_nonneg _)

/-- **All moments `m ≥ 1` vanish.** -/
theorem hasSum_sCoef_mul_point_pow {m : ℕ} (h1 : 1 ≤ m) :
    HasSum (fun i : Idx => sCoef i * point i ^ m) 0 := by
  have hsum := summable_sCoef_mul_point_pow m
  have hσ := hsum.hasSum.sigma (fun k => hasSum_fintype (fun j => sCoef ⟨k, j⟩ * point ⟨k, j⟩ ^ m))
  have heq : (fun k => ∑ j, sCoef ⟨k, j⟩ * point ⟨k, j⟩ ^ m) = sStageSum m := rfl
  rw [heq] at hσ
  rw [← hσ.unique (hasSum_sStageSum h1)]
  exact hsum.hasSum

/-! ## The node series -/

/-- **The node series is constant near the origin.** -/
theorem tsum_sCoef_div_eq_tsum {t : ℂ} (ht : ‖t‖ < 1 / 10) :
    ∑' i : Idx, sCoef i / (1 - t * point i) = ∑' i : Idx, sCoef i := by
  set r : ℝ := 10 * ‖t‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hxt : ∀ i, ‖t * point i‖ ≤ r := fun i => by
    rw [norm_mul, hr]; nlinarith [norm_point_le i, norm_nonneg t]
  have hsumU :
      Summable (Function.uncurry fun (i : Idx) (m : ℕ) => sCoef i * (t * point i) ^ m) := by
    refine Summable.of_norm_bounded (summable_norm_sCoef.mul_of_nonneg
      (summable_geometric_of_lt_one hr0 hr1) (fun _ => norm_nonneg _) (fun _ => by positivity))
      (fun q => ?_)
    show ‖sCoef q.1 * (t * point q.1) ^ q.2‖ ≤ ‖sCoef q.1‖ * r ^ q.2
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hxt _) _) (norm_nonneg _)
  have hinner : ∀ i : Idx, ∑' m : ℕ, sCoef i * (t * point i) ^ m = sCoef i / (1 - t * point i) := by
    intro i
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one ((hxt i).trans_lt hr1), div_eq_mul_inv]
  have hcol : ∀ m : ℕ, ∑' i : Idx, sCoef i * (t * point i) ^ m =
      if m = 0 then ∑' i : Idx, sCoef i else 0 := by
    intro m
    have e : (fun i : Idx => sCoef i * (t * point i) ^ m) =
        fun i => t ^ m * (sCoef i * point i ^ m) := by
      funext i; ring
    rw [e, tsum_mul_left]
    split_ifs with hm
    · subst hm; simp
    · rw [(hasSum_sCoef_mul_point_pow (Nat.one_le_iff_ne_zero.mpr hm)).tsum_eq, mul_zero]
  calc ∑' i : Idx, sCoef i / (1 - t * point i)
      = ∑' i : Idx, ∑' m : ℕ, sCoef i * (t * point i) ^ m := tsum_congr fun i => (hinner i).symm
    _ = ∑' m : ℕ, ∑' i : Idx, sCoef i * (t * point i) ^ m := hsumU.tsum_comm.symm
    _ = ∑' i : Idx, sCoef i := by
        simp only [hcol]
        rw [tsum_ite_eq]

/-- **The node series has a simple pole at the isolated node `4/5`.** -/
theorem norm_tsum_sCoef_div_ge {t : ℂ} (h1 : 0 < ‖t - 4 / 5‖) (h2 : ‖t - 4 / 5‖ < 1 / 40) :
    4 / 5 / ‖t - 4 / 5‖ - 30 * ∑' i : Idx, ‖sCoef i‖ ≤
      ‖∑' i : Idx, sCoef i / (1 - t * point i)‖ := by
  classical
  have ht : (31 / 40 : ℝ) ≤ ‖t‖ := by
    have h45 : ‖(4 / 5 : ℂ)‖ = 4 / 5 := by
      rw [show (4 / 5 : ℂ) = ((4 / 5 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have h := norm_sub_norm_le (4 / 5 : ℂ) (4 / 5 - t)
    rw [sub_sub_cancel, norm_sub_rev, h45] at h
    linarith
  have hfar : ∀ i : Idx, i ≠ base → ‖sCoef i / (1 - t * point i)‖ ≤ 30 * ‖sCoef i‖ := by
    intro i hi
    have hx := four_thirds_le_norm_point hi
    have hden : (1 / 30 : ℝ) ≤ ‖1 - t * point i‖ := by
      have h := norm_sub_norm_le (t * point i) 1
      rw [norm_mul, norm_one, norm_sub_rev] at h
      nlinarith [norm_nonneg t, norm_nonneg (point i)]
    rw [norm_div, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (sCoef i)]
  set g : Idx → ℂ := fun i => sCoef i / (1 - t * point i) with hg
  have hgs : Summable g := by
    refine Summable.of_norm_bounded_eventually (summable_norm_sCoef.mul_left 30) ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton base).subset fun i hi => ?_
    simp only [Set.mem_setOf_eq, not_le] at hi
    by_contra hne
    exact (not_le.mpr hi) (hfar i hne)
  rw [hgs.tsum_eq_add_tsum_ite base]
  have hbase : g base = 1 / (1 - t * (5 / 4)) := rfl
  have hbase_norm : ‖g base‖ = 4 / 5 / ‖t - 4 / 5‖ := by
    rw [hbase, show (1 : ℂ) - t * (5 / 4) = -(5 / 4) * (t - 4 / 5) by ring, norm_div, norm_one,
      norm_mul, norm_neg, norm_five_fourths]
    field_simp
  have hrest : ‖∑' n : Idx, (if n = base then 0 else g n)‖ ≤ 30 * ∑' i : Idx, ‖sCoef i‖ := by
    have hb : ∀ n : Idx, ‖(if n = base then 0 else g n)‖ ≤ 30 * ‖sCoef n‖ := by
      intro n
      split_ifs with hn
      · rw [norm_zero]; positivity
      · exact hfar n hn
    have hs : Summable fun n : Idx => ‖(if n = base then 0 else g n)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (summable_norm_sCoef.mul_left 30)
    calc ‖∑' n : Idx, (if n = base then 0 else g n)‖
        ≤ ∑' n : Idx, ‖(if n = base then 0 else g n)‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : Idx, 30 * ‖sCoef n‖ := hs.tsum_le_tsum hb (summable_norm_sCoef.mul_left 30)
      _ = 30 * ∑' i : Idx, ‖sCoef i‖ := tsum_mul_left
  have htri := norm_sub_norm_le (g base) (-(∑' n : Idx, (if n = base then 0 else g n)))
  rw [sub_neg_eq_add, norm_neg, hbase_norm] at htri
  linarith

/-- **A sector-positive Wolff measure with `p`-summable weights for every `p > 0`.** The weights
satisfy `|c_i| ≤ 2 Re c_i`, and for every `ε > 0` all but finitely many satisfy
`|Im c_i| ≤ ε Re c_i`. -/
theorem exists_sector_wolff_measure :
    ∃ (ι : Type) (_ : Countable ι) (x : ι → ℂ) (c : ι → ℂ) (i₀ : ι), Function.Injective x ∧
      (∀ i, 5 / 4 ≤ ‖x i‖ ∧ ‖x i‖ ≤ 10) ∧ x i₀ = 5 / 4 ∧ c i₀ = 1 ∧
      (∀ i, i ≠ i₀ → 4 / 3 ≤ ‖x i‖) ∧ (∀ i, ‖c i‖ ≤ 2 * (c i).re) ∧
      (∀ ε : ℝ, 0 < ε → {i | ε * (c i).re < |(c i).im|}.Finite) ∧
      (∀ p : ℝ, 0 < p → Summable fun i => ‖c i‖ ^ p) ∧
      ∀ m : ℕ, 1 ≤ m → HasSum (fun i => c i * x i ^ m) 0 :=
  ⟨Idx, inferInstance, point, sCoef, base, point_injective,
    fun i => ⟨norm_point_ge i, norm_point_le i⟩, rfl, rfl, fun _ hi => four_thirds_le_norm_point hi,
    sCoef_sector, fun _ hε => finite_sCoef_arg hε, fun _ hp => summable_norm_sCoef_rpow hp,
    fun _ hm => hasSum_sCoef_mul_point_pow hm⟩

end

end GaloisForLFunctions.HTGeometry.CircleQuadratureSector
