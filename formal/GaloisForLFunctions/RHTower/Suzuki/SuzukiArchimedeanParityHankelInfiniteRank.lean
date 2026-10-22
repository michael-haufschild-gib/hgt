import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Infinite rank of Suzuki's archimedean parity Hankel kernel

The regular positive-lag kernel in Suzuki's parity Hankel block is

`h(z) = exp(z/2) - exp(-5z/2)/(1-exp(-2z))`.

Distinct nonnegative translates of `h` are linearly independent on every nonempty positive
interval.  Consequently its sum kernel `h(x+y)` has no finite separation-rank representation on
any positive open square.  The proof clears all translate denominators and evaluates at their
distinct complex poles; analytic continuation transfers a relation on an arbitrary real interval
to the cleared entire relation.

This is the analytic core of the class-level obstruction to identifying Suzuki's literal even and
odd restricted-Weil blocks as finite-rank perturbations of one another.
-/

namespace RHTower

open Complex Filter

noncomputable section

def archDenominator {n : ℕ} (u : Fin n → ℂ) (k : Fin n) (z : ℂ) : ℂ :=
  1 - Complex.exp (-2 * (z + u k))

def clearedArchRelation {n : ℕ} (u c : Fin n → ℂ) (z : ℂ) : ℂ :=
  (∑ j, c j * Complex.exp ((z + u j) / 2)) *
      ∏ k, archDenominator u k z -
    ∑ j, c j * Complex.exp (-5 * (z + u j) / 2) *
      ∏ k ∈ Finset.univ.erase j, archDenominator u k z

def archHankelProfile (z : ℂ) : ℂ :=
  Complex.exp (z / 2) -
    Complex.exp (-5 * z / 2) / (1 - Complex.exp (-2 * z))

def archTranslatePacket {n : ℕ} (u c : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ j, c j * archHankelProfile (z + u j)

theorem fullDenominator_mul_archTranslatePacket
    {n : ℕ} (u c : Fin n → ℂ) (z : ℂ)
    (hden : ∀ j, archDenominator u j z ≠ 0) :
    (∏ k, archDenominator u k z) * archTranslatePacket u c z =
      clearedArchRelation u c z := by
  rw [archTranslatePacket, Finset.mul_sum, clearedArchRelation]
  rw [Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hj]
  rw [Finset.sdiff_singleton_eq_erase]
  simp only [archHankelProfile]
  rw [show 1 - Complex.exp (-2 * (z + u j)) =
      archDenominator u j z by rfl]
  field_simp [hden j]

theorem coeff_zero {n : ℕ} {u c : Fin n → ℂ}
    (hsep : ∀ j k, j ≠ k →
      Complex.exp (-2 * (u k - u j)) ≠ 1)
    (hzero : ∀ z, clearedArchRelation u c z = 0) :
    c = 0 := by
  funext j
  have hdenSelf : archDenominator u j (-u j) = 0 := by
    simp [archDenominator]
  have hfull : (∏ k, archDenominator u k (-u j)) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) hdenSelf
  have hother : ∀ l ∈ Finset.univ, l ≠ j →
      c l * Complex.exp (-5 * (-u j + u l) / 2) *
        ∏ k ∈ Finset.univ.erase l, archDenominator u k (-u j) = 0 := by
    intro l hl hlj
    have hjmem : j ∈ Finset.univ.erase l := by
      exact Finset.mem_erase.mpr ⟨Ne.symm hlj, Finset.mem_univ j⟩
    have hprod :
        (∏ k ∈ Finset.univ.erase l, archDenominator u k (-u j)) = 0 := by
      exact Finset.prod_eq_zero hjmem hdenSelf
    rw [hprod, mul_zero]
  have hsingle :
      (∑ l, c l * Complex.exp (-5 * (-u j + u l) / 2) *
        ∏ k ∈ Finset.univ.erase l, archDenominator u k (-u j)) =
        c j * ∏ k ∈ Finset.univ.erase j, archDenominator u k (-u j) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro l hl hlj
      exact hother l hl hlj
    · simp
  have hprodNe :
      (∏ k ∈ Finset.univ.erase j, archDenominator u k (-u j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    rw [archDenominator, sub_ne_zero]
    simpa [sub_eq_add_neg, add_comm] using
      (hsep j k (Ne.symm hkj)).symm
  have hj := hzero (-u j)
  rw [clearedArchRelation, hfull, mul_zero, zero_sub, hsingle] at hj
  exact (mul_eq_zero.mp (neg_eq_zero.mp hj)).resolve_right hprodNe

theorem coeff_zero_real_nodes {n : ℕ} {y : Fin n → ℝ} {c : Fin n → ℂ}
    (hy : Function.Injective y)
    (hzero : ∀ z, clearedArchRelation (fun j => (y j : ℂ)) c z = 0) :
    c = 0 := by
  apply coeff_zero ?_ hzero
  intro j k hjk hcollision
  have hreal :
      Real.exp (-2 * (y k - y j)) = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_exp]
    norm_num at hcollision ⊢
    simpa only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_sub] using hcollision
  have harg : -2 * (y k - y j) = 0 := by
    apply Real.exp_injective
    simpa using hreal
  have : y k = y j := by linarith
  exact hjk (hy this.symm)

theorem clearedArchRelation_eq_zero_of_posReal
    {n : ℕ} {u c : Fin n → ℂ}
    (hpos : ∀ x : ℝ, 0 < x →
      clearedArchRelation u c (x : ℂ) = 0) :
    ∀ z, clearedArchRelation u c z = 0 := by
  let f : ℂ → ℂ := clearedArchRelation u c
  have hdiff : Differentiable ℂ f := by
    dsimp [f]
    unfold clearedArchRelation archDenominator
    fun_prop
  have han : AnalyticOnNhd ℂ f Set.univ :=
    hdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hclosure :
      (1 : ℂ) ∈ closure ({z | f z = 0} \ {(1 : ℂ)}) := by
    let s : ℕ → ℂ := fun n => 1 + 1 / ((n : ℂ) + 1)
    have hs : Tendsto s atTop (nhds (1 : ℂ)) := by
      simpa [s] using
        (tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)) :
          Tendsto (fun n : ℕ => (1 : ℂ) + 1 / ((n : ℂ) + 1))
            atTop (nhds ((1 : ℂ) + 0)))
    apply mem_closure_of_tendsto hs
    filter_upwards [] with n
    constructor
    · change f (1 + 1 / ((n : ℂ) + 1)) = 0
      have hx : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by positivity
      simpa [f, s, Complex.ofReal_add, Complex.ofReal_div,
        Complex.ofReal_natCast] using hpos (1 + 1 / ((n : ℝ) + 1)) hx
    · change 1 + 1 / ((n : ℂ) + 1) ≠ 1
      have hden : (n : ℂ) + 1 ≠ 0 := by
        have hnat : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        simpa using hnat
      intro h
      have hq : 1 / ((n : ℂ) + 1) = 0 := by
        calc
          1 / ((n : ℂ) + 1) =
              (1 + 1 / ((n : ℂ) + 1)) - 1 := by ring
          _ = 1 - 1 := by rw [h]
          _ = 0 := by ring
      exact one_div_ne_zero hden hq
  have hall := han.eqOn_zero_of_preconnected_of_mem_closure
    isPreconnected_univ (Set.mem_univ (1 : ℂ)) hclosure
  intro z
  exact hall (Set.mem_univ z)

theorem clearedArchRelation_eq_zero_of_posReal_lt
    {n : ℕ} {u c : Fin n → ℂ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x : ℝ, 0 < x → x < b →
      clearedArchRelation u c (x : ℂ) = 0) :
    ∀ z, clearedArchRelation u c z = 0 := by
  let f : ℂ → ℂ := clearedArchRelation u c
  have hdiff : Differentiable ℂ f := by
    dsimp [f]
    unfold clearedArchRelation archDenominator
    fun_prop
  have han : AnalyticOnNhd ℂ f Set.univ :=
    hdiff.differentiableOn.analyticOnNhd isOpen_univ
  let center : ℝ := b / 2
  let s : ℕ → ℂ := fun n =>
    (center : ℂ) + (b / 4 : ℂ) / ((n : ℂ) + 1)
  have hs : Tendsto s atTop (nhds (center : ℂ)) := by
    have hzero :
        Tendsto (fun n : ℕ => (b / 4 : ℂ) / ((n : ℂ) + 1))
          atTop (nhds 0) := by
      have hconst :
          Tendsto (fun _ : ℕ => (b / 4 : ℂ)) atTop
            (nhds (b / 4 : ℂ)) := tendsto_const_nhds
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        hconst.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
    simpa only [s, add_zero] using tendsto_const_nhds.add hzero
  have hclosure :
      (center : ℂ) ∈ closure ({z | f z = 0} \ {(center : ℂ)}) := by
    apply mem_closure_of_tendsto hs
    filter_upwards [] with n
    have hdenReal : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hinvPos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hdenReal
    have hinvLe : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ hdenReal]
      nlinarith
    have hxPos : 0 < center + (b / 4) / ((n : ℝ) + 1) := by
      dsimp only [center]
      positivity
    have hxLt : center + (b / 4) / ((n : ℝ) + 1) < b := by
      have hterm :
          (b / 4) / ((n : ℝ) + 1) ≤ b / 4 := by
        calc
          (b / 4) / ((n : ℝ) + 1) =
              (b / 4) * (1 / ((n : ℝ) + 1)) := by
                rw [div_eq_mul_inv, one_div]
          _ ≤ b / 4 := by
            simpa using
              mul_le_mul_of_nonneg_left hinvLe
                (show 0 ≤ b / 4 by positivity)
      dsimp only [center]
      nlinarith [hterm]
    constructor
    · change f ((center : ℂ) + (b / 4 : ℂ) / ((n : ℂ) + 1)) = 0
      simpa [f, s, Complex.ofReal_add, Complex.ofReal_div,
        Complex.ofReal_natCast] using
        hpos (center + (b / 4) / ((n : ℝ) + 1)) hxPos hxLt
    · change
        (center : ℂ) + (b / 4 : ℂ) / ((n : ℂ) + 1) ≠ (center : ℂ)
      have hden : (n : ℂ) + 1 ≠ 0 := by
        have hnat : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        simpa using hnat
      have hbC : (b / 4 : ℂ) ≠ 0 := by
        exact_mod_cast (div_ne_zero hb.ne' (by norm_num : (4 : ℝ) ≠ 0))
      intro heq
      have hq : (b / 4 : ℂ) / ((n : ℂ) + 1) = 0 := by
        calc
          (b / 4 : ℂ) / ((n : ℂ) + 1) =
              ((center : ℂ) + (b / 4 : ℂ) / ((n : ℂ) + 1)) -
                (center : ℂ) := by ring
          _ = 0 := by rw [heq]; ring
      exact (div_ne_zero hbC hden) hq
  have hall := han.eqOn_zero_of_preconnected_of_mem_closure
    isPreconnected_univ (Set.mem_univ (center : ℂ)) hclosure
  intro z
  exact hall (Set.mem_univ z)

theorem archTranslatePacket_coeff_zero_of_posReal
    {n : ℕ} {y : Fin n → ℝ} {c : Fin n → ℂ}
    (hy : Function.Injective y)
    (hyNonneg : ∀ j, 0 ≤ y j)
    (hpacket : ∀ x : ℝ, 0 < x →
      archTranslatePacket (fun j => (y j : ℂ)) c (x : ℂ) = 0) :
    c = 0 := by
  apply coeff_zero_real_nodes hy
  apply clearedArchRelation_eq_zero_of_posReal
  intro x hx
  have hden : ∀ j,
      archDenominator (fun k => (y k : ℂ)) j (x : ℂ) ≠ 0 := by
    intro j
    rw [archDenominator, sub_ne_zero]
    intro hcollision
    have hreal : Real.exp (-2 * (x + y j)) = 1 := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_exp]
      norm_num at hcollision ⊢
      simpa only [Complex.ofReal_ofNat, Complex.ofReal_neg,
        Complex.ofReal_mul, Complex.ofReal_add] using hcollision.symm
    have harg : -2 * (x + y j) = 0 := by
      apply Real.exp_injective
      simpa using hreal
    nlinarith [hyNonneg j]
  have hclear :=
    fullDenominator_mul_archTranslatePacket
      (fun j => (y j : ℂ)) c (x : ℂ) hden
  rw [hpacket x hx, mul_zero] at hclear
  exact hclear.symm

theorem archTranslatePacket_coeff_zero_of_posReal_lt
    {n : ℕ} {y : Fin n → ℝ} {c : Fin n → ℂ} {b : ℝ}
    (hb : 0 < b)
    (hy : Function.Injective y)
    (hyNonneg : ∀ j, 0 ≤ y j)
    (hpacket : ∀ x : ℝ, 0 < x → x < b →
      archTranslatePacket (fun j => (y j : ℂ)) c (x : ℂ) = 0) :
    c = 0 := by
  apply coeff_zero_real_nodes hy
  apply clearedArchRelation_eq_zero_of_posReal_lt hb
  intro x hx hxb
  have hden : ∀ j,
      archDenominator (fun k => (y k : ℂ)) j (x : ℂ) ≠ 0 := by
    intro j
    rw [archDenominator, sub_ne_zero]
    intro hcollision
    have hreal : Real.exp (-2 * (x + y j)) = 1 := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_exp]
      norm_num at hcollision ⊢
      simpa only [Complex.ofReal_ofNat, Complex.ofReal_neg,
        Complex.ofReal_mul, Complex.ofReal_add] using hcollision.symm
    have harg : -2 * (x + y j) = 0 := by
      apply Real.exp_injective
      simpa using hreal
    nlinarith [hyNonneg j]
  have hclear :=
    fullDenominator_mul_archTranslatePacket
      (fun j => (y j : ℂ)) c (x : ℂ) hden
  rw [hpacket x hx hxb, mul_zero] at hclear
  exact hclear.symm

/-- Archimedean Hankel kernel on the positive quadrant. -/
def archHankelKernel (x y : ℝ) : ℂ :=
  archHankelProfile ((x + y : ℝ) : ℂ)

/-- Distinct nonnegative translates of the archimedean Hankel profile are linearly independent
on every nonempty positive interval. -/
theorem linearIndependent_archHankelKernel_translates_on_posReal_lt
    {n : ℕ} {y : Fin n → ℝ} {b : ℝ}
    (hb : 0 < b) (hy : Function.Injective y)
    (hyNonneg : ∀ j, 0 ≤ y j) :
    LinearIndependent ℂ
      (fun j : Fin n => fun x : Set.Ioo (0 : ℝ) b =>
        archHankelKernel x.1 (y j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum j
  have hpacket : ∀ x : ℝ, 0 < x → x < b →
      archTranslatePacket (fun k => (y k : ℂ)) c (x : ℂ) = 0 := by
    intro x hx hxb
    have hxsum := congrFun hsum
      (⟨x, hx, hxb⟩ : Set.Ioo (0 : ℝ) b)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hxsum
    simpa only [archTranslatePacket, archHankelKernel,
      Complex.ofReal_add] using hxsum
  have hc :=
    archTranslatePacket_coeff_zero_of_posReal_lt hb hy hyNonneg hpacket
  exact congrFun hc j

/-- A positive-quadrant kernel has separation rank at most `r` when it is a sum of `r`
separated products there. -/
def HasPositiveSeparationRankAtMost
    (r : ℕ) (K : ℝ → ℝ → ℂ) : Prop :=
  ∃ f g : Fin r → ℝ → ℂ, ∀ x y : ℝ, 0 < x → 0 < y →
    K x y = ∑ k, f k x * g k y

/-- Separation-rank bound on a nonempty positive open square. -/
def HasPositiveOpenSquareSeparationRankAtMost
    (r : ℕ) (b : ℝ) (K : ℝ → ℝ → ℂ) : Prop :=
  ∃ f g : Fin r → ℝ → ℂ, ∀ x y : ℝ,
    0 < x → x < b → 0 < y → y < b →
      K x y = ∑ k, f k x * g k y

/-- The smooth archimedean Hankel profile has no finite separation-rank representation on the
positive quadrant. -/
theorem archHankelKernel_not_hasPositiveSeparationRankAtMost (r : ℕ) :
    ¬ HasPositiveSeparationRankAtMost r archHankelKernel := by
  rintro ⟨f, g, hsep⟩
  let T : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun c k => ∑ j, c j * g k ((j : ℕ) + 1)
      map_add' := by
        intro c d
        funext k
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        funext k
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          RingHom.id_apply]
        apply Finset.sum_congr rfl
        intro j hj
        ring }
  have hrank :
      Module.finrank ℂ (Fin r → ℂ) <
        Module.finrank ℂ (Fin (r + 1) → ℂ) := by
    simp
  have hker : LinearMap.ker T ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hrank
  rw [Submodule.ne_bot_iff] at hker
  obtain ⟨c, hcKer, hcNe⟩ := hker
  have hTc : T c = 0 := LinearMap.mem_ker.mp hcKer
  have hrow (k : Fin r) :
      (∑ j, c j * g k ((j : ℕ) + 1)) = 0 := by
    exact congrFun hTc k
  let y : Fin (r + 1) → ℝ := fun j => (j : ℕ) + 1
  have hy : Function.Injective y := by
    intro j k hjk
    apply Fin.ext
    dsimp only [y] at hjk
    have hnat : (j : ℕ) + 1 = (k : ℕ) + 1 := by
      exact_mod_cast hjk
    omega
  have hyNonneg : ∀ j, 0 ≤ y j := by
    intro j
    dsimp only [y]
    positivity
  have hpacket : ∀ x : ℝ, 0 < x →
      archTranslatePacket (fun j => (y j : ℂ)) c (x : ℂ) = 0 := by
    intro x hx
    rw [archTranslatePacket]
    calc
      (∑ j, c j * archHankelProfile ((x : ℂ) + (y j : ℂ))) =
          ∑ j, c j * ∑ k, f k x * g k (y j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show archHankelProfile ((x : ℂ) + (y j : ℂ)) =
            archHankelKernel x (y j) by
          simp only [archHankelKernel, Complex.ofReal_add]]
        rw [hsep x (y j) hx (by
          dsimp only [y]
          positivity)]
      _ = ∑ j, ∑ k, c j * (f k x * g k (y j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
      _ = ∑ k, ∑ j, c j * (f k x * g k (y j)) :=
        Finset.sum_comm
      _ = ∑ k, f k x * ∑ j, c j * g k (y j) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by
        have hyVal (j : Fin (r + 1)) : y j = ((j : ℕ) + 1 : ℝ) := rfl
        simp_rw [hyVal, hrow]
        simp
  have hcZero :=
    archTranslatePacket_coeff_zero_of_posReal hy hyNonneg hpacket
  exact hcNe hcZero

/-- The infinite separation-rank obstruction already occurs on every nonempty positive open
square. -/
theorem archHankelKernel_not_hasPositiveOpenSquareSeparationRankAtMost
    (r : ℕ) {b : ℝ} (hb : 0 < b) :
    ¬ HasPositiveOpenSquareSeparationRankAtMost r b archHankelKernel := by
  rintro ⟨f, g, hsep⟩
  let y : Fin (r + 1) → ℝ := fun j =>
    b * (((j : ℕ) : ℝ) + 1) / (r + 2)
  have hy : Function.Injective y := by
    intro j k hjk
    apply Fin.ext
    have hden : ((r + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hb0 : b ≠ 0 := hb.ne'
    dsimp only [y] at hjk
    field_simp [hden] at hjk
    have hcast : ((j : ℕ) : ℝ) = ((k : ℕ) : ℝ) := by
      nlinarith
    exact_mod_cast hcast
  have hyPos : ∀ j, 0 < y j := by
    intro j
    dsimp only [y]
    positivity
  have hyLt : ∀ j, y j < b := by
    intro j
    have hj : (j : ℕ) + 1 < r + 2 := by omega
    dsimp only [y]
    change b * (((j : ℕ) : ℝ) + 1) / (((r : ℕ) : ℝ) + 2) < b
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 2)]
    have hjReal : (((j : ℕ) : ℝ) + 1) < (r + 2 : ℕ) := by
      exact_mod_cast hj
    norm_num at hjReal ⊢
    exact mul_lt_mul_of_pos_left hjReal hb
  let T : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun c k => ∑ j, c j * g k (y j)
      map_add' := by
        intro c d
        funext k
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        funext k
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          RingHom.id_apply]
        apply Finset.sum_congr rfl
        intro j hj
        ring }
  have hrank :
      Module.finrank ℂ (Fin r → ℂ) <
        Module.finrank ℂ (Fin (r + 1) → ℂ) := by
    simp
  have hker : LinearMap.ker T ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hrank
  rw [Submodule.ne_bot_iff] at hker
  obtain ⟨c, hcKer, hcNe⟩ := hker
  have hTc : T c = 0 := LinearMap.mem_ker.mp hcKer
  have hrow (k : Fin r) :
      (∑ j, c j * g k (y j)) = 0 := congrFun hTc k
  have hpacket : ∀ x : ℝ, 0 < x → x < b →
      archTranslatePacket (fun j => (y j : ℂ)) c (x : ℂ) = 0 := by
    intro x hx hxb
    rw [archTranslatePacket]
    calc
      (∑ j, c j * archHankelProfile ((x : ℂ) + (y j : ℂ))) =
          ∑ j, c j * ∑ k, f k x * g k (y j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show archHankelProfile ((x : ℂ) + (y j : ℂ)) =
            archHankelKernel x (y j) by
          simp only [archHankelKernel, Complex.ofReal_add]]
        rw [hsep x (y j) hx hxb (hyPos j) (hyLt j)]
      _ = ∑ j, ∑ k, c j * (f k x * g k (y j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
      _ = ∑ k, ∑ j, c j * (f k x * g k (y j)) :=
        Finset.sum_comm
      _ = ∑ k, f k x * ∑ j, c j * g k (y j) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by
        simp_rw [hrow]
        simp
  have hcZero :=
    archTranslatePacket_coeff_zero_of_posReal_lt hb hy
      (fun j => (hyPos j).le) hpacket
  exact hcNe hcZero

end

end RHTower
