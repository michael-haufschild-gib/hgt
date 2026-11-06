import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheHyperbolicCameraSeesIsolatedZeros
import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount

/-!
# The Lorentzian mass has an exponential tail

At `δ = cL`, `L = log T`, the Lorentzian mass of all zeros is `≍ 1/c` on average, and it is rarely larger:

`|{t ∈ (T, 2T] : Σ_ρ m_ρ/(1 + δ²(γ_ρ − t)²) > K κ}| ≪ T e^{−κ/120000} + L T^{1/2}`

for `κ ≥ max(κ₀, 1/c)` (`exists_volume_lorentz_mass_gt_le`). This is an exponential tail, unconditional, and it holds for all zeros at
once, however deep.

**Mechanism.** The corpus bounds the number of zeros within `κ'/L` of `t` by `10κ'` off measure `≪ T e^{−κ'/120000}`
(`exists_volume_localZeroCount_gt_le_exp`). Apply it at the scales `κ' = 2^j κ` up to unit distance. A shell at scale `2^j κ/L` holds at most
`10·2^j κ` zeros, each of Lorentzian weight `≤ (c 2^{j−1} κ)^{−2}`, so the shells sum to `≪ 1/(c²κ)`. Beyond unit distance the weight is
`≪ δ^{−2}/(1 + d²)`, and the unit-scale mass is `≪ L` everywhere.

**Consequence.** Near-line zeros, whose camera weight is `≤ e^A` times their Lorentzian weight, can block a zero of amplitude `e^x` only on measure
`≪ T exp(−c' e^{x−A})`. At every rate, the only possible competitors of a deep zero are comparably deep zeros.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23
open GaloisForLFunctions.SquareRootThreshold (sum_mult_le_tsum_copies)

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The Lorentzian kernel at scale `1/δ`. -/
def lorentzKernel (δ d : ℝ) : ℝ := 1 / (1 + δ ^ 2 * d ^ 2)

theorem lorentzKernel_nonneg (δ d : ℝ) : 0 ≤ lorentzKernel δ d := by
  unfold lorentzKernel
  positivity

theorem lorentzKernel_le_one (δ d : ℝ) : lorentzKernel δ d ≤ 1 := by
  unfold lorentzKernel
  rw [div_le_one (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg δ) (sq_nonneg d)]

theorem lorentzKernel_le_of_le {δ R d : ℝ} (hδ : 0 < δ) (hR : 0 < R) (h : R < |d|) :
    lorentzKernel δ d ≤ 1 / (δ ^ 2 * R ^ 2) := by
  unfold lorentzKernel
  refine one_div_le_one_div_of_le (by positivity) ?_
  have h2 : R ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs d]
    exact pow_le_pow_left₀ hR.le h.le 2
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg δ)
  linarith

/-! ### The count at one scale, with multiplicity -/

/-- Off the exceptional set of the local count, a multiplicity-weighted family within `R` has mass at most `x`. -/
theorem sum_mult_within_le {t R x : ℝ}
    (hgood : ¬ ∃ F : Finset XiZeroCopy, (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ R) ∧ x < F.card)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier) :
    ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * (if |ρ.im - t| ≤ R then (1 : ℝ) else 0) ≤ x := by
  classical
  set g : ℂ → ℝ := fun ρ => if |ρ.im - t| ≤ R then (1 : ℝ) else 0 with hg
  have hg0 : ∀ ρ, 0 ≤ g ρ := fun ρ => by
    simp only [hg]
    split_ifs <;> norm_num
  have hsum : Summable fun q : XiZeroCopy => g (q.1 : ℂ) := by
    refine Summable.of_nonneg_of_le (fun q => hg0 _) (fun q => ?_)
      ((summable_lorentzMassTerm t).mul_left (1 + R ^ 2))
    simp only [hg, lorentzMassTerm]
    split_ifs with h
    · rw [mul_one_div, le_div_iff₀ (by positivity), one_mul]
      have h2 : (t - ((q.1 : ℂ)).im) ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs, abs_sub_comm]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      linarith
    · positivity
  refine (sum_mult_le_tsum_copies g (fun q => hg0 _) hsum S hS).trans ?_
  refine Real.tsum_le_of_sum_le (fun q => hg0 _) fun s => ?_
  have hcard : ∑ q ∈ s, g (q.1 : ℂ) = ((s.filter fun q : XiZeroCopy =>
      |((q.1 : ℂ)).im - t| ≤ R).card : ℝ) := by
    simp only [hg]
    rw [Finset.sum_boole]
  rw [hcard]
  by_contra hlt
  exact hgood ⟨s.filter fun q : XiZeroCopy => |((q.1 : ℂ)).im - t| ≤ R,
    fun q hq => (Finset.mem_filter.mp hq).2, not_le.mp hlt⟩

/-- A multiplicity-weighted family has Lorentzian mass at unit scale at most `lorentzMass`. -/
theorem sum_mult_unit_le_lorentzMass (t : ℝ) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier) :
    ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - ρ.im) ^ 2)) ≤ lorentzMass t :=
  sum_mult_le_tsum_copies (fun ρ => 1 / (1 + (t - ρ.im) ^ 2))
    (fun q => by positivity) (summable_lorentzMassTerm t) S hS

/-! ### The pointwise bound -/

/-- Shells of a Lorentzian kernel: an Abel decomposition over the scales `R 0 < R 1 < …`. -/
theorem lorentzKernel_le_shells {δ : ℝ} (hδ : 0 < δ) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j) (J : ℕ) (d : ℝ) :
    lorentzKernel δ d ≤ (if |d| ≤ R 0 then 1 else 0) +
      (∑ j ∈ Finset.range J, 1 / (δ ^ 2 * R j ^ 2) * (if |d| ≤ R (j + 1) then 1 else 0)) +
      (if |d| ≤ R J then 0 else lorentzKernel δ d) := by
  induction J with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    by_cases h : |d| ≤ R 0
    · rw [if_pos h, if_pos h, add_zero]
      exact lorentzKernel_le_one δ d
    · rw [if_neg h, if_neg h, zero_add]
  | succ J ih =>
    refine ih.trans ?_
    rw [Finset.sum_range_succ]
    have hnn : 0 ≤ 1 / (δ ^ 2 * R J ^ 2) := by
      have := hR J
      positivity
    by_cases h1 : |d| ≤ R J
    · rw [if_pos h1]
      by_cases h2 : |d| ≤ R (J + 1)
      · rw [if_pos h2, if_pos h2]
        linarith
      · rw [if_neg h2, if_neg h2]
        have := lorentzKernel_nonneg δ d
        linarith
    · rw [if_neg h1]
      have hk := lorentzKernel_le_of_le hδ (hR J) (not_le.mp h1)
      by_cases h2 : |d| ≤ R (J + 1)
      · rw [if_pos h2, if_pos h2]
        linarith
      · rw [if_neg h2, if_neg h2]
        linarith

/-- **The pointwise bound at a good height.** If the local counts hold at all scales `R j = 2^j κ/L`, then every finite family of zeros has
Lorentzian mass `≤ 10κ + 40/(c²κ) + 1025 δ^{−2} lorentzMass`. -/
theorem sum_lorentz_le_of_good {c L κ t : ℝ} (hc : 0 < c) (hL : 0 < L) (hκ : 0 < κ) {J : ℕ}
    (hJ : 1 / 32 ≤ 2 ^ J * κ / L)
    (hgood : ∀ j ∈ Finset.range (J + 1), ¬ ∃ F : Finset XiZeroCopy,
      (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ 2 ^ j * κ / L) ∧ 10 * (2 ^ j * κ / L * L) < F.card)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier) :
    ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * lorentzKernel (c * L) (ρ.im - t) ≤
      10 * κ + 40 / (c ^ 2 * κ) + 1025 / (c * L) ^ 2 * lorentzMass t := by
  classical
  have hδ : 0 < c * L := by positivity
  set R : ℕ → ℝ := fun j => 2 ^ j * κ / L with hRdef
  have hR : ∀ j, 0 < R j := fun j => by
    simp only [hRdef]
    positivity
  have hRL : ∀ j, R j * L = 2 ^ j * κ := fun j => by
    simp only [hRdef]
    field_simp
  -- the count at each scale
  have hcount : ∀ j ∈ Finset.range (J + 1), ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) *
      (if |ρ.im - t| ≤ R j then (1 : ℝ) else 0) ≤ 10 * (2 ^ j * κ) := by
    intro j hj
    have h := sum_mult_within_le (hgood j hj) S hS
    rwa [hRL j] at h
  -- pointwise shells, summed with the multiplicities
  have hm : ∀ ρ, (0 : ℝ) ≤ zetaZeroConfig.mult ρ := fun ρ => Nat.cast_nonneg _
  have hfar : ∀ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) *
      (if |ρ.im - t| ≤ R J then 0 else lorentzKernel (c * L) (ρ.im - t)) ≤
      1025 / (c * L) ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - ρ.im) ^ 2))) := by
    intro ρ _
    split_ifs with h
    · rw [mul_zero]
      have := hm ρ
      positivity
    · have h1 : R J < |ρ.im - t| := not_le.mp h
      have h2 : (1 / 32 : ℝ) < |ρ.im - t| := lt_of_le_of_lt hJ h1
      have h3 : (1 : ℝ) / 1024 ≤ (ρ.im - t) ^ 2 := by
        rw [← sq_abs]
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 32) h2.le 2
        calc (1 : ℝ) / 1024 = (1 / 32) ^ 2 := by norm_num
          _ ≤ _ := this
      have hδ2 : 0 < (c * L) ^ 2 := by positivity
      have hk : lorentzKernel (c * L) (ρ.im - t) ≤ 1025 / (c * L) ^ 2 * (1 / (1 + (t - ρ.im) ^ 2)) := by
        unfold lorentzKernel
        have e : (t - ρ.im) ^ 2 = (ρ.im - t) ^ 2 := by ring
        rw [e, div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        nlinarith [mul_nonneg hδ2.le (sq_nonneg (ρ.im - t))]
      calc _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (1025 / (c * L) ^ 2 * (1 / (1 + (t - ρ.im) ^ 2))) :=
            mul_le_mul_of_nonneg_left hk (hm ρ)
        _ = _ := by ring
  have hsumShell : ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * lorentzKernel (c * L) (ρ.im - t) ≤
      (∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * (if |ρ.im - t| ≤ R 0 then (1 : ℝ) else 0)) +
      (∑ j ∈ Finset.range J, 1 / ((c * L) ^ 2 * R j ^ 2) *
        ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * (if |ρ.im - t| ≤ R (j + 1) then (1 : ℝ) else 0)) +
      ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) *
        (if |ρ.im - t| ≤ R J then 0 else lorentzKernel (c * L) (ρ.im - t)) := by
    have e : (∑ j ∈ Finset.range J, 1 / ((c * L) ^ 2 * R j ^ 2) *
        ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * (if |ρ.im - t| ≤ R (j + 1) then (1 : ℝ) else 0)) =
        ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * ∑ j ∈ Finset.range J, 1 / ((c * L) ^ 2 * R j ^ 2) *
          (if |ρ.im - t| ≤ R (j + 1) then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ρ _ => ?_
    have h := lorentzKernel_le_shells hδ hR J (ρ.im - t)
    calc _ ≤ (zetaZeroConfig.mult ρ : ℝ) * _ := mul_le_mul_of_nonneg_left h (hm ρ)
      _ = _ := by ring
  refine hsumShell.trans ?_
  have h0 := hcount 0 (Finset.mem_range.mpr (by omega))
  rw [pow_zero, one_mul] at h0
  -- the shells sum geometrically
  have hshell : ∑ j ∈ Finset.range J, 1 / ((c * L) ^ 2 * R j ^ 2) *
      ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * (if |ρ.im - t| ≤ R (j + 1) then (1 : ℝ) else 0) ≤
      40 / (c ^ 2 * κ) := by
    have hterm : ∀ j ∈ Finset.range J, 1 / ((c * L) ^ 2 * R j ^ 2) *
        ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * (if |ρ.im - t| ≤ R (j + 1) then (1 : ℝ) else 0) ≤
        20 / (c ^ 2 * κ) * (1 / 2) ^ j := by
      intro j hj
      have hj' : j + 1 ∈ Finset.range (J + 1) := by
        rw [Finset.mem_range] at hj ⊢
        omega
      have h1 := hcount (j + 1) hj'
      have hpos : 0 ≤ 1 / ((c * L) ^ 2 * R j ^ 2) := by
        have := hR j
        positivity
      refine (mul_le_mul_of_nonneg_left h1 hpos).trans (le_of_eq ?_)
      simp only [hRdef]
      rw [one_div_pow, pow_succ]
      field_simp
      ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hgeom : ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j ≤ 2 := by
      have h := sum_geometric_two_le J
      exact h
    calc 20 / (c ^ 2 * κ) * ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j
        ≤ 20 / (c ^ 2 * κ) * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = _ := by ring
  -- the far part
  have hfarSum : ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) *
      (if |ρ.im - t| ≤ R J then 0 else lorentzKernel (c * L) (ρ.im - t)) ≤
      1025 / (c * L) ^ 2 * lorentzMass t := by
    refine (Finset.sum_le_sum hfar).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_mult_unit_le_lorentzMass t S hS) (by positivity)
  linarith

/-! ### The exponential tail -/

/-- `φ(κ) ≤ 2051 e^{−κ/120000}` for the rate of the corpus local count. -/
theorem local_count_rate_le {κ : ℝ} (hκ : 0 ≤ κ) :
    Real.exp (-(κ / 120000)) / (1 / 2) + (κ ^ 2 * Real.exp (-(κ / 16)) +
        Real.exp (-(κ * (1 / 2) / 15))) ≤ 2051 * Real.exp (-(κ / 120000)) := by
  have he := Real.exp_pos (-(κ / 120000))
  have h1 : Real.exp (-(κ * (1 / 2) / 15)) ≤ Real.exp (-(κ / 120000)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h2 : κ ^ 2 * Real.exp (-(κ / 16)) ≤ 2048 * Real.exp (-(κ / 120000)) := by
    have hsplit : Real.exp (-(κ / 16)) ≤ Real.exp (-(κ / 120000)) * Real.exp (-(κ / 32)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hq := Real.quadratic_le_exp_of_nonneg (x := κ / 32) (by positivity)
    have hq2 : κ ^ 2 * Real.exp (-(κ / 32)) ≤ 2048 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      nlinarith
    calc κ ^ 2 * Real.exp (-(κ / 16))
        ≤ κ ^ 2 * (Real.exp (-(κ / 120000)) * Real.exp (-(κ / 32))) :=
          mul_le_mul_of_nonneg_left hsplit (by positivity)
      _ = (κ ^ 2 * Real.exp (-(κ / 32))) * Real.exp (-(κ / 120000)) := by ring
      _ ≤ 2048 * Real.exp (-(κ / 120000)) := mul_le_mul_of_nonneg_right hq2 he.le
  have e : Real.exp (-(κ / 120000)) / (1 / 2) = 2 * Real.exp (-(κ / 120000)) := by ring
  rw [e]
  linarith

/-- The dyadic exponentials sum to at most twice the first one. -/
theorem sum_exp_two_pow_le {κ : ℝ} (hκ : 120000 ≤ κ) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.exp (-(2 ^ j * κ / 120000)) ≤ 2 * Real.exp (-(κ / 120000)) := by
  set q := Real.exp (-(κ / 120000)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 / 2 := by
    have h1 : 1 ≤ κ / 120000 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    have h2 : q ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    have h3 := Real.add_one_le_exp (1 : ℝ)
    have h4 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (by linarith)
    linarith
  have hterm : ∀ j ∈ Finset.range J, Real.exp (-(2 ^ j * κ / 120000)) ≤ q * (1 / 2) ^ j := by
    intro j _
    have h1 : ((j : ℝ) + 1) ≤ 2 ^ j := by
      have := Nat.lt_two_pow_self (n := j)
      exact_mod_cast this
    have h2 : Real.exp (-(2 ^ j * κ / 120000)) ≤ q ^ (j + 1) := by
      rw [hq, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      push_cast
      have h3 : ((j : ℝ) + 1) * (κ / 120000) ≤ 2 ^ j * κ / 120000 := by
        have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ κ / 120000)
        calc _ ≤ _ := this
          _ = _ := by ring
      linarith
    refine h2.trans ?_
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0.le hq1 j) hq0.le
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hgeom : ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j ≤ 2 := sum_geometric_two_le J
  calc q * ∑ j ∈ Finset.range J, ((1 : ℝ) / 2) ^ j ≤ q * 2 :=
        mul_le_mul_of_nonneg_left hgeom hq0.le
    _ = _ := by ring

/-- The dyadic scales up to unit distance. -/
theorem exists_dyadic_scale {L κ : ℝ} (hL : 0 < L) (hκ1 : 1 ≤ κ) (hfit : 32 * κ ≤ L) :
    ∃ J : ℕ, 2 ^ J * κ / L ≤ 1 / 16 ∧ 1 / 32 ≤ 2 ^ J * κ / L ∧ (J : ℝ) + 1 ≤ L + 1 := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨J, hJ⟩ : ∃ J, J = Nat.log 2 ⌊L / (16 * κ)⌋₊ := ⟨_, rfl⟩
  have hratio : 2 ≤ L / (16 * κ) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hfl1 : ⌊L / (16 * κ)⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊L / (16 * κ)⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  have hpow1 : ((2 : ℝ) ^ J) ≤ L / (16 * κ) := by
    have h1 : 2 ^ J ≤ ⌊L / (16 * κ)⌋₊ := by
      rw [hJ]
      exact Nat.pow_log_le_self 2 hfl1
    have h2 : ((2 ^ J : ℕ) : ℝ) ≤ (⌊L / (16 * κ)⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by positivity))
  have hpow2 : L / (16 * κ) < 2 ^ (J + 1) := by
    have h1 : ⌊L / (16 * κ)⌋₊ < 2 ^ (J + 1) := by
      rw [hJ]
      exact Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 := Nat.lt_floor_add_one (L / (16 * κ))
    have h3 : ((⌊L / (16 * κ)⌋₊ : ℝ) + 1) ≤ 2 ^ (J + 1) := by
      have : ⌊L / (16 * κ)⌋₊ + 1 ≤ 2 ^ (J + 1) := h1
      exact_mod_cast this
    linarith
  refine ⟨J, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hL]
    rw [le_div_iff₀ (by positivity)] at hpow1
    nlinarith
  · rw [le_div_iff₀ hL]
    rw [div_lt_iff₀ (by positivity), pow_succ] at hpow2
    nlinarith
  · have h1 : (J : ℝ) + 1 ≤ 2 ^ J := by
      have := Nat.lt_two_pow_self (n := J)
      exact_mod_cast this
    have h2 : L / (16 * κ) ≤ L := div_le_self hL.le (by nlinarith)
    linarith

/-- The sum of the exceptional measures at the dyadic scales. -/
theorem sum_bad_le {C₁ T κ L : ℝ} (hC₁ : 0 < C₁) (hT : 0 < T) (hκ : 120000 ≤ κ) {J : ℕ}
    (hJL : (J : ℝ) + 1 ≤ L + 1) :
    ∑ j ∈ Finset.range (J + 1), (C₁ * T * (2051 * Real.exp (-(2 ^ j * κ / 120000))) +
        C₁ * T ^ ((1 : ℝ) / 2)) ≤
      (4102 * C₁ + C₁) * T * Real.exp (-(κ / 120000)) +
        (4102 * C₁ + C₁) * (L + 1) * T ^ ((1 : ℝ) / 2) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hs := sum_exp_two_pow_le hκ (J + 1)
  have hT12 : 0 ≤ T ^ ((1 : ℝ) / 2) := by positivity
  have h1 : C₁ * T * (2051 * ∑ j ∈ Finset.range (J + 1), Real.exp (-(2 ^ j * κ / 120000))) ≤
      4102 * C₁ * T * Real.exp (-(κ / 120000)) := by
    have := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ C₁ * T * 2051)
    linarith
  have hL1 : 0 ≤ L + 1 := le_trans (by positivity) hJL
  have h2 : ((J + 1 : ℕ) : ℝ) * (C₁ * T ^ ((1 : ℝ) / 2)) ≤
      (L + 1) * (C₁ * T ^ ((1 : ℝ) / 2)) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    push_cast
    exact hJL
  have h3 : 0 ≤ C₁ * T * Real.exp (-(κ / 120000)) := by positivity
  have h4 : 0 ≤ 4102 * C₁ * (L + 1) * T ^ ((1 : ℝ) / 2) := by positivity
  have e1 : (4102 * C₁ + C₁) * T * Real.exp (-(κ / 120000)) =
      4102 * C₁ * T * Real.exp (-(κ / 120000)) + C₁ * T * Real.exp (-(κ / 120000)) := by ring
  have e2 : (4102 * C₁ + C₁) * (L + 1) * T ^ ((1 : ℝ) / 2) =
      (L + 1) * (C₁ * T ^ ((1 : ℝ) / 2)) + 4102 * C₁ * (L + 1) * T ^ ((1 : ℝ) / 2) := by ring
  rw [e1, e2]
  linarith

/-- The bound on the far and shell parts, at a good height. -/
theorem mass_le_of_shells {c κ Cf K s far : ℝ} (hc : 0 < c) (hκ1 : 1 ≤ κ) (hκc : 1 / c ≤ κ)
    (hCf : 0 ≤ Cf) (hK : 50 + Cf ≤ K) (hfar : far ≤ Cf)
    (hs : s ≤ 10 * κ + 40 / (c ^ 2 * κ) + far) : s ≤ K * κ := by
  have hκ0 : 0 < κ := by linarith
  have h1 : 1 ≤ κ * c := by
    rwa [div_le_iff₀ hc] at hκc
  have hcκ : 1 / (c ^ 2 * κ) ≤ κ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : 40 / (c ^ 2 * κ) ≤ 40 * κ := by
    have e : 40 / (c ^ 2 * κ) = 40 * (1 / (c ^ 2 * κ)) := by ring
    rw [e]
    linarith
  have h3 : Cf ≤ Cf * κ := le_mul_of_one_le_right hCf hκ1
  have h4 : (50 + Cf) * κ ≤ K * κ := mul_le_mul_of_nonneg_right hK hκ0.le
  nlinarith

/-- **The Lorentzian mass at a fitting `κ`.** -/
theorem volume_lorentz_mass_gt_le_of_fit {C₁ κ₁ T L c κ Cf K : ℝ} (hC₁ : 0 < C₁) (hT0 : 0 < T)
    (hL : 0 < L) (hc : 0 < c) (hκ₁ : κ₁ ≤ κ) (hκ2 : 120000 ≤ κ) (hκc : 1 / c ≤ κ) (hCf : 0 ≤ Cf)
    (hK : 50 + Cf ≤ K) (hfit : 32 * κ ≤ L)
    (hfarle : ∀ t ∈ Ioc T (2 * T), 1025 / (c * L) ^ 2 * lorentzMass t ≤ Cf)
    (hT : ∀ R : ℝ, 0 < R → R ≤ 1 / 16 → κ₁ ≤ R * L →
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ F : Finset XiZeroCopy,
          (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ R) ∧ 10 * (R * L) < F.card} ≤
        ENNReal.ofReal (C₁ * T * (Real.exp (-(R * L / 120000)) / (1 / 2) +
          ((R * L) ^ 2 * Real.exp (-(R * L / 16)) +
            Real.exp (-(R * L * (1 / 2) / 15)))) + C₁ * T ^ ((1 : ℝ) / 2))) :
    volume {t | t ∈ Ioc T (2 * T) ∧ ∃ F : Finset zetaZeroConfig.carrier,
      K * κ < ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * lorentzKernel (c * L) ((ρ : ℂ).im - t)} ≤
    ENNReal.ofReal ((4102 * C₁ + C₁) * T * Real.exp (-(κ / 120000)) +
      (4102 * C₁ + C₁) * (L + 1) * T ^ ((1 : ℝ) / 2)) := by
  classical
  have hκ1 : (1 : ℝ) ≤ κ := by linarith
  have hκ0 : 0 < κ := by linarith
  obtain ⟨J, hRJ, hRJlow, hJL⟩ := exists_dyadic_scale hL hκ1 hfit
  have hRj : ∀ j ∈ Finset.range (J + 1), 2 ^ j * κ / L ≤ 1 / 16 := by
    intro j hj
    have hj' : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj'
    refine le_trans ?_ hRJ
    gcongr
  have hBadvol : ∀ j ∈ Finset.range (J + 1),
      volume {t | t ∈ Icc T (2 * T) ∧ ∃ F : Finset XiZeroCopy,
        (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ 2 ^ j * κ / L) ∧ 10 * (2 ^ j * κ / L * L) < F.card} ≤
      ENNReal.ofReal (C₁ * T * (2051 * Real.exp (-(2 ^ j * κ / 120000))) +
        C₁ * T ^ ((1 : ℝ) / 2)) := by
    intro j hj
    have hR0 : 0 < 2 ^ j * κ / L := by positivity
    have hRL : 2 ^ j * κ / L * L = 2 ^ j * κ := by field_simp
    have hκj : κ₁ ≤ 2 ^ j * κ / L * L := by
      rw [hRL]
      have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    refine (hT _ hR0 (hRj j hj) hκj).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hRL]
    have hrate := local_count_rate_le (κ := 2 ^ j * κ) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left hrate (by positivity : 0 ≤ C₁ * T)
    linarith
  have hsub : {t | t ∈ Ioc T (2 * T) ∧ ∃ F : Finset zetaZeroConfig.carrier,
      K * κ < ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * lorentzKernel (c * L) ((ρ : ℂ).im - t)} ⊆
      ⋃ j ∈ Finset.range (J + 1), {t | t ∈ Icc T (2 * T) ∧ ∃ F : Finset XiZeroCopy,
        (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ 2 ^ j * κ / L) ∧ 10 * (2 ^ j * κ / L * L) < F.card} := by
    rintro t ⟨ht, F, hF⟩
    by_contra hnot
    have hgood : ∀ j ∈ Finset.range (J + 1), ¬ ∃ F : Finset XiZeroCopy,
        (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ 2 ^ j * κ / L) ∧ 10 * (2 ^ j * κ / L * L) < F.card := by
      intro j hj hex
      apply hnot
      exact Set.mem_biUnion (Finset.mem_coe.mpr hj) ⟨⟨ht.1.le, ht.2⟩, hex⟩
    have hpt := sum_lorentz_le_of_good hc hL hκ0 hRJlow hgood (F.image Subtype.val)
      (fun ρ hρ => by
        obtain ⟨ρ', -, rfl⟩ := Finset.mem_image.mp hρ
        exact ρ'.2)
    rw [Finset.sum_image Subtype.val_injective.injOn] at hpt
    exact absurd hF (not_lt.mpr (mass_le_of_shells hc hκ1 hκc hCf hK (hfarle t ht) hpt))
  refine (measure_mono hsub).trans ?_
  refine (measure_biUnion_finset_le _ _).trans ?_
  refine (Finset.sum_le_sum hBadvol).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (sum_bad_le hC₁ hT0 hκ2 hJL)

/-- **The Lorentzian mass at a large `κ`.** The bound holds at every height. -/
theorem lorentz_mass_le_of_large {L c κ Cξ K : ℝ} (hL1 : 1 ≤ L) (hLd : 64 ≤ c ^ 2 * L)
    (hCξ : 0 ≤ Cξ) (hκ0 : 0 < κ) (hK : 32 * 8 * (Cξ + 2) ≤ K) (hbig : L < 32 * κ) {t : ℝ}
    (hunit : lorentzMass t ≤ 8 * (Cξ + 2) * L) (F : Finset zetaZeroConfig.carrier) :
    ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * lorentzKernel (c * L) ((ρ : ℂ).im - t) ≤ K * κ := by
  classical
  have hL0 : 0 < L := by linarith
  have h2 := sum_mult_unit_le_lorentzMass t (F.image Subtype.val) (fun ρ hρ => by
    obtain ⟨ρ', -, rfl⟩ := Finset.mem_image.mp hρ
    exact ρ'.2)
  rw [Finset.sum_image Subtype.val_injective.injOn] at h2
  have hδ1 : 1 ≤ (c * L) ^ 2 := by
    have e : (c * L) ^ 2 = c ^ 2 * L * L := by ring
    rw [e]
    nlinarith
  have hterm : ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * lorentzKernel (c * L) ((ρ : ℂ).im - t) ≤
      ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2)) := by
    refine Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    unfold lorentzKernel
    refine one_div_le_one_div_of_le (by positivity) ?_
    have e : (t - (ρ : ℂ).im) ^ 2 = ((ρ : ℂ).im - t) ^ 2 := by ring
    rw [e]
    nlinarith [sq_nonneg ((ρ : ℂ).im - t)]
  have h5 : 8 * (Cξ + 2) * L ≤ 32 * 8 * (Cξ + 2) * κ := by
    have := mul_le_mul_of_nonneg_left hbig.le (by positivity : 0 ≤ 8 * (Cξ + 2))
    linarith
  have h6 : 32 * 8 * (Cξ + 2) * κ ≤ K * κ := mul_le_mul_of_nonneg_right hK hκ0.le
  linarith

/-- **The Lorentzian mass has an exponential tail.** At `δ = cL`, for `κ ≥ max(κ₀, 1/c)`, all finite families of zeros have Lorentzian mass
at most `K κ` off measure `C T e^{−κ/120000} + C (L + 1) T^{1/2}` in `(T, 2T]`. -/
theorem exists_volume_lorentz_mass_gt_le :
    ∃ K C κ₀ : ℝ, 1 ≤ K ∧ 0 < C ∧ 1 ≤ κ₀ ∧ ∀ᶠ T : ℝ in atTop, ∀ c κ : ℝ, 0 < c →
      64 / c ^ 2 ≤ Real.log T → κ₀ ≤ κ → 1 / c ≤ κ →
      volume {t | t ∈ Ioc T (2 * T) ∧ ∃ F : Finset zetaZeroConfig.carrier,
        K * κ < ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * lorentzKernel (c * Real.log T) ((ρ : ℂ).im - t)} ≤
      ENNReal.ofReal (C * T * Real.exp (-(κ / 120000)) +
        C * (Real.log T + 1) * T ^ ((1 : ℝ) / 2)) := by
  classical
  obtain ⟨C₁, κ₁, hC₁, hκ₁, hev⟩ := exists_volume_localZeroCount_gt_le_exp
  have hCξ := xiLineTwoLogDerivConstant_nonneg
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = 1025 / 64 * 8 * (xiLineTwoLogDerivConstant + 2) := ⟨_, rfl⟩
  have hCf0 : 0 ≤ Cf := by
    rw [hCf]
    positivity
  refine ⟨50 + Cf + 32 * 8 * (xiLineTwoLogDerivConstant + 2), 4102 * C₁ + C₁, max κ₁ 120000,
    by nlinarith, by positivity, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 4, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with T hT hT4 hL1 c κ hc0 hLd hκ₀ hκc
  have hT0 : 0 < T := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hL1 hLd hT ⊢
  have hL0 : 0 < L := by linarith
  have hκ1 : κ₁ ≤ κ := (le_max_left _ _).trans hκ₀
  have hκ2 : (120000 : ℝ) ≤ κ := (le_max_right _ _).trans hκ₀
  have hκ0 : 0 < κ := by linarith
  have hunit : ∀ t ∈ Ioc T (2 * T), lorentzMass t ≤ 8 * (xiLineTwoLogDerivConstant + 2) * L := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hM := lorentzMass_le_log t
    rw [abs_of_nonneg ht0] at hM
    have hlog : Real.log (t + 4) ≤ 2 * L := by
      have h1 : t + 4 ≤ T ^ 2 := by nlinarith [ht.2]
      calc Real.log (t + 4) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) h1
        _ = 2 * L := by rw [Real.log_pow, ← hLdef]; norm_num
    have : xiLineTwoLogDerivConstant ≤ xiLineTwoLogDerivConstant * L :=
      le_mul_of_one_le_right hCξ hL1
    nlinarith
  have hcL : 64 ≤ c ^ 2 * L := by
    rw [div_le_iff₀ (by positivity)] at hLd
    linarith
  have hfarle : ∀ t ∈ Ioc T (2 * T), 1025 / (c * L) ^ 2 * lorentzMass t ≤ Cf := by
    intro t ht
    have h1 := hunit t ht
    have hsum : 0 ≤ xiLineTwoLogDerivConstant + 2 := by linarith
    have h2 : 1025 / (c * L) ^ 2 * lorentzMass t ≤
        1025 / (c * L) ^ 2 * (8 * (xiLineTwoLogDerivConstant + 2) * L) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine h2.trans ?_
    have e : 1025 / (c * L) ^ 2 * (8 * (xiLineTwoLogDerivConstant + 2) * L) =
        1025 * 8 * (xiLineTwoLogDerivConstant + 2) / (c ^ 2 * L) := by
      field_simp
    rw [e, hCf, div_le_iff₀ (by positivity)]
    have h3 : 1025 / 64 * 8 * (xiLineTwoLogDerivConstant + 2) * 64 ≤
        1025 / 64 * 8 * (xiLineTwoLogDerivConstant + 2) * (c ^ 2 * L) :=
      mul_le_mul_of_nonneg_left hcL (by positivity)
    linarith
  have hK1 : 50 + Cf ≤ 50 + Cf + 32 * 8 * (xiLineTwoLogDerivConstant + 2) := by
    have : 0 ≤ 32 * 8 * (xiLineTwoLogDerivConstant + 2) := by positivity
    linarith
  have hK2 : 32 * 8 * (xiLineTwoLogDerivConstant + 2) ≤
      50 + Cf + 32 * 8 * (xiLineTwoLogDerivConstant + 2) := by linarith
  rcases le_or_gt (32 * κ) L with hfit | hbig
  · exact volume_lorentz_mass_gt_le_of_fit hC₁ hT0 hL0 hc0 hκ1 hκ2 hκc hCf0 hK1 hfit hfarle hT
  · have hempty : {t | t ∈ Ioc T (2 * T) ∧ ∃ F : Finset zetaZeroConfig.carrier,
        (50 + Cf + 32 * 8 * (xiLineTwoLogDerivConstant + 2)) * κ <
          ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * lorentzKernel (c * L) ((ρ : ℂ).im - t)} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_exists, not_lt]
      intro ht F
      exact lorentz_mass_le_of_large hL1 hcL hCξ hκ0 hK2 hbig (hunit t ht) F
    rw [hempty, measure_empty]
    exact zero_le

end GaloisForLFunctions.MultiscaleMollifiedZetaField
