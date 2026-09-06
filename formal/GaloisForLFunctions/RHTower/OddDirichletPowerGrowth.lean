import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Pi

/-!
# Sharp growth boundary for odd Dirichlet coefficient powers

Group finite words in positive integer labels by their integer product. For nonnegative
letter weights of total mass `A`, the sum of squared grouped coefficients lies between
`A^(2*k)/(k+1)^r` and `A^(2*k)`, where `r` is the number of labels. Thus an exponential
bound with base `C` holds at every depth exactly when `A ≤ C`.

For labels `3,5,...,2*r+1` weighted by `n^(-σ)`, a single bound uniform in both cutoff
and depth exists exactly for `σ > 1`. The initial coefficients are square summable
exactly for `σ > 1/2`. Odd products of the literal replacement coefficients
`b(1)=0`, `b(n)=(-1)^n` for `n≥2` have one common sign at each depth.

All energies are formed from finite integer-product fibers. No zero-location input
or conditional infinite-product rearrangement is used.
-/

noncomputable section
open scoped BigOperators
open Finset Filter Topology
namespace RHTower.OddDirichletPowerGrowth

/-- Weighted collision energy of a finite map, formed before summing distinct outputs. -/
def collision {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (w : α → ℝ) : ℝ :=
  ∑ a, ∑ b, if f a = f b then w a * w b else 0

private theorem collision_eq_fibers {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (w : α → ℝ) :
    collision f w = ∑ y : β, (∑ a ∈ univ.filter (fun a => f a = y), w a) ^ 2 := by
  classical
  let F : β → ℝ := fun y => ∑ a ∈ univ.filter (fun a => f a = y), w a
  have hf : (∑ y : β, F y ^ 2) = ∑ a : α, w a * F (f a) := by
    calc
      _ = ∑ y : β, ∑ a ∈ univ.filter (fun a => f a = y), w a * F (f a) := by
        apply sum_congr rfl
        intro y _
        rw [pow_two]
        change (∑ a ∈ univ.filter (fun a => f a = y), w a) * F y = _
        rw [sum_mul]
        apply sum_congr rfl
        intro a ha
        rw [(mem_filter.mp ha).2]
      _ = _ := sum_fiberwise univ f (fun a => w a * F (f a))
  change collision f w = ∑ y, F y ^ 2
  rw [hf]
  simp only [collision, F, mul_sum, sum_filter, mul_ite, mul_zero, eq_comm]

private theorem mass_sq_le_collision {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) (w : α → ℝ) :
    (∑ a, w a) ^ 2 ≤ (Fintype.card β : ℝ) * collision f w := by
  rw [collision_eq_fibers, ← sum_fiberwise univ f w]
  simpa using (sq_sum_le_card_mul_sum_sq (s := univ)
    (f := fun y : β => ∑ a ∈ univ.filter (fun a => f a = y), w a))

private theorem collision_mono {α β γ : Type*} [Fintype α]
    [DecidableEq β] [DecidableEq γ] (f : α → β) (g : α → γ) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hfg : ∀ a b, f a = f b → g a = g b) :
    collision f w ≤ collision g w := by
  apply sum_le_sum
  intro a _
  apply sum_le_sum
  intro b _
  by_cases h : f a = f b
  · simp [h, hfg a b h]
  · simp only [h, if_false]
    split_ifs
    · exact mul_nonneg (hw a) (hw b)
    · exact le_rfl

private theorem collision_le_mass_sq {α β : Type*} [Fintype α]
    [DecidableEq β] (f : α → β) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) :
    collision f w ≤ (∑ a, w a) ^ 2 := by
  rw [pow_two, sum_mul]
  apply sum_le_sum
  intro a _
  rw [mul_sum]
  apply sum_le_sum
  intro b _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hw a) (hw b)

/-- The bounded vector of letter counts in a finite word. -/
def histogram {k r : ℕ} (u : Fin k → Fin r) (j : Fin r) : Fin (k + 1) :=
  ⟨(univ.filter (fun i => u i = j)).card,
    by have h := card_filter_le (s := (univ : Finset (Fin k))) (p := fun i => u i = j)
       simpa using Nat.lt_succ_of_le h⟩

private theorem prod_eq_histogram {k r : ℕ} (m : Fin r → ℕ) (u : Fin k → Fin r) :
    ∏ i, m (u i) = ∏ j, m j ^ (histogram u j : ℕ) := by
  rw [← prod_fiberwise' univ u m]
  simp only [prod_const, histogram]

private theorem histogram_eq_implies_product_eq {k r : ℕ} (m : Fin r → ℕ)
    (u v : Fin k → Fin r) (h : histogram u = histogram v) :
    (∏ i, m (u i)) = ∏ i, m (v i) := by
  rw [prod_eq_histogram, prod_eq_histogram, h]

private theorem word_mass {k r : ℕ} (w : Fin r → ℝ) :
    (∑ u : Fin k → Fin r, ∏ i, w (u i)) = (∑ j, w j) ^ k := by
  rw [← Fintype.piFinset_univ, ← prod_univ_sum]
  simp

/-- Squared coefficient mass after words are grouped by their integer products. -/
def wordEnergy {r : ℕ} (m : Fin r → ℕ) (w : Fin r → ℝ) (k : ℕ) : ℝ :=
  collision (fun u : Fin k → Fin r => ∏ i, m (u i)) (fun u => ∏ i, w (u i))

/-- Letter-count groups give a polynomial-loss lower bound for actual product collisions. -/
theorem wordEnergy_lower {r : ℕ} (m : Fin r → ℕ) (w : Fin r → ℝ)
    (hw : ∀ j, 0 ≤ w j) (k : ℕ) :
    (∑ j, w j) ^ (2 * k) ≤ ((k + 1 : ℕ) : ℝ) ^ r * wordEnergy m w k := by
  have h := mass_sq_le_collision (@histogram k r) (fun u => ∏ i, w (u i))
  have hm := collision_mono (@histogram k r) (fun u => ∏ i, m (u i))
    (fun u => ∏ i, w (u i)) (fun u => prod_nonneg fun i _ => hw (u i))
    (histogram_eq_implies_product_eq m)
  have hmul := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (Fintype.card (Fin r → Fin (k+1))))
  rw [word_mass, ← pow_mul] at h
  simpa [Fintype.card_fun, mul_comm k 2, wordEnergy] using h.trans hmul

/-- Keeping every pair of words gives the total-mass upper bound. -/
theorem wordEnergy_upper {r : ℕ} (m : Fin r → ℕ) (w : Fin r → ℝ)
    (hw : ∀ j, 0 ≤ w j) (k : ℕ) :
    wordEnergy m w k ≤ (∑ j, w j) ^ (2 * k) := by
  have h := collision_le_mass_sq (fun u : Fin k → Fin r => ∏ i, m (u i))
    (fun u => ∏ i, w (u i)) (fun u => prod_nonneg fun i _ => hw (u i))
  rw [word_mass, ← pow_mul] at h
  simpa [wordEnergy, mul_comm k 2] using h

private theorem mass_le_of_polynomial_power_bound {A C : ℝ} (hC : 0 ≤ C) (r : ℕ)
    (h : ∀ k : ℕ, A ^ (2*k) ≤ ((k+1 : ℕ) : ℝ)^r * C^(2*k)) : A ≤ C := by
  by_contra hn
  have hCA : C < A := lt_of_not_ge hn
  have hAp : 0 < A := lt_of_le_of_lt hC hCA
  have hCp : 0 < C := by
    rcases hC.eq_or_lt with hc | hc
    · have h1 := h 1
      rw [← hc] at h1
      norm_num at h1
      nlinarith [sq_pos_of_pos hAp]
    · exact hc
  let R : ℝ := (A/C)^2
  have hR : 1 < R := by
    have hq : 1 < A/C := (one_lt_div hCp).mpr hCA
    dsimp [R]
    nlinarith
  have hRp : 0 < R := lt_trans zero_lt_one hR
  have ht := ((tendsto_pow_const_div_const_pow_of_one_lt r hR).comp
    (tendsto_add_atTop_nat 1)).mul_const R
  have he (k : ℕ) : (((k+1 : ℕ) : ℝ)^r / R^(k+1))*R =
      ((k+1 : ℕ) : ℝ)^r / R^k := by
    rw [pow_succ]
    field_simp
  simp only [Function.comp_apply, zero_mul] at ht
  simp_rw [he] at ht
  have hl (k : ℕ) : 1 ≤ ((k+1 : ℕ) : ℝ)^r / R^k := by
    apply (le_div_iff₀ (pow_pos hRp k)).mpr
    rw [one_mul]
    change ((A/C)^2)^k ≤ _
    rw [← pow_mul, div_pow]
    exact (div_le_iff₀ (pow_pos hCp (2*k))).mpr (h k)
  obtain ⟨k,hk⟩ := (ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))).exists
  exact (not_lt_of_ge (hl k)) hk

/-- The least base controlling every convolution depth is exactly the total letter mass. -/
theorem wordEnergy_exponential_bound_iff {r : ℕ} (m : Fin r → ℕ)
    (w : Fin r → ℝ) (hw : ∀ j, 0 ≤ w j) {C : ℝ} (hC : 0 ≤ C) :
    (∀ k, wordEnergy m w k ≤ C^(2*k)) ↔ ∑ j, w j ≤ C := by
  constructor
  · intro h
    apply mass_le_of_polynomial_power_bound hC r
    intro k
    exact (wordEnergy_lower m w hw k).trans
      (mul_le_mul_of_nonneg_left (h k) (by positivity))
  · intro h k
    exact (wordEnergy_upper m w hw k).trans
      (pow_le_pow_left₀ (sum_nonneg fun j _ => hw j) h _)

/-- The weight of the positive odd integer `2*j+3`. -/
def oddWeight (σ : ℝ) (j : ℕ) : ℝ := ((2*j+3 : ℕ) : ℝ)^(-σ)

/-- Coefficient energy of the kth power of the first r weighted odd integers above one. -/
def oddEnergy (σ : ℝ) (r k : ℕ) : ℝ :=
  wordEnergy (fun j : Fin r => 2*(j:ℕ)+3) (fun j => oddWeight σ j) k

private theorem oddWeight_nonneg (σ : ℝ) (j : ℕ) : 0 ≤ oddWeight σ j := by
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem summable_oddWeight {σ : ℝ} (hσ : 1 < σ) : Summable (oddWeight σ) := by
  have h := Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)
  exact h.comp_injective (i := fun j : ℕ => 2*j+3) (by intro a b hab; dsimp at hab; omega)

set_option maxHeartbeats 800000 in
private theorem not_summable_oddWeight {σ : ℝ} (hσ : σ ≤ 1) :
    ¬ Summable (oddWeight σ) := by
  intro hs
  have hh : Summable (fun j : ℕ => (1:ℝ)/((j:ℝ)+1)) := by
    apply (hs.mul_left 3).of_nonneg_of_le (fun j => by positivity)
    intro j
    have hp : 0 < ((2*j+3 : ℕ) : ℝ) := by positivity
    have hpow : 1/((2*j+3 : ℕ) : ℝ) ≤ oddWeight σ j := by
      have hh := Real.rpow_le_rpow_of_exponent_le
        (show (1:ℝ) ≤ ((2*j+3 : ℕ) : ℝ) by exact_mod_cast (by omega : 1 ≤ 2*j+3))
        (show (-1:ℝ) ≤ -σ by linarith)
      simpa [oddWeight, Real.rpow_neg_one, one_div] using hh
    have hrat : (1:ℝ)/((j:ℝ)+1) ≤ 3/((2*j+3 : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) hp).mpr
      push_cast
      nlinarith
    exact hrat.trans (by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤3))
  have hh' : Summable (fun j : ℕ => (((j+1 : ℕ):ℝ)^1)⁻¹) := by
    simpa [one_div] using hh
  have hh'' : Summable (fun n : ℕ => ((n:ℝ)^1)⁻¹) := (summable_nat_add_iff 1).mp hh'
  have := (Real.summable_nat_pow_inv (p := 1)).mp hh''
  norm_num at this

/-- One exponential bound controls all odd cutoffs and all depths exactly when `σ > 1`. -/
theorem oddEnergy_uniform_exponential_bound_iff (σ : ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ r k : ℕ, oddEnergy σ r k ≤ C^(2*k)) ↔ 1 < σ := by
  constructor
  · rintro ⟨C,hC,h⟩
    by_contra hn
    apply not_summable_oddWeight (le_of_not_gt hn)
    apply summable_of_sum_range_le (oddWeight_nonneg σ)
    intro r
    have hm := (wordEnergy_exponential_bound_iff
      (fun j : Fin r => 2*(j:ℕ)+3) (fun j => oddWeight σ j)
      (fun j => oddWeight_nonneg σ j) hC).mp (h r)
    simpa [Fin.sum_univ_eq_sum_range] using hm
  · intro hσ
    have hs := summable_oddWeight hσ
    refine ⟨∑' j, oddWeight σ j, tsum_nonneg (oddWeight_nonneg σ), ?_⟩
    intro r
    apply (wordEnergy_exponential_bound_iff _ _ (fun j => oddWeight_nonneg σ j)
      (tsum_nonneg (oddWeight_nonneg σ))).mpr
    simpa [Fin.sum_univ_eq_sum_range] using
      hs.sum_le_tsum (range r) (fun j _ => oddWeight_nonneg σ j)


/-- The finite set of integer products attained by words of a fixed length. -/
def wordProducts {r : ℕ} (m : Fin r → ℕ) (k : ℕ) : Finset ℕ :=
  univ.image (fun u : Fin k → Fin r => ∏ i, m (u i))

/-- The exact finite Dirichlet coefficient at one integer product. -/
def wordCoefficient {r : ℕ} (m : Fin r → ℕ) (w : Fin r → ℝ) (k n : ℕ) : ℝ :=
  ∑ u : Fin k → Fin r, if (∏ i, m (u i)) = n then ∏ i, w (u i) else 0

/-- The collision definition agrees with the sum of squared Dirichlet coefficients. -/
theorem wordEnergy_eq_coefficient_squares {r : ℕ} (m : Fin r → ℕ)
    (w : Fin r → ℝ) (k : ℕ) :
    wordEnergy m w k = ∑ n ∈ wordProducts m k, (wordCoefficient m w k n)^2 := by
  classical
  let f := fun u : Fin k → Fin r => ∏ i, m (u i)
  let W := fun u : Fin k → Fin r => ∏ i, w (u i)
  let F := fun n : ℕ => ∑ u ∈ univ.filter (fun u => f u = n), W u
  have hF (n : ℕ) : F n = wordCoefficient m w k n := by
    simp only [F, wordCoefficient, sum_filter, f, W]
  have hf : (∑ n ∈ wordProducts m k, F n^2) = ∑ u, W u * F (f u) := by
    calc
      _ = ∑ n ∈ wordProducts m k,
          ∑ u ∈ univ.filter (fun u => f u = n), W u * F (f u) := by
        apply sum_congr rfl
        intro n _
        rw [pow_two]
        change (∑ u ∈ univ.filter (fun u => f u = n), W u) * F n = _
        rw [sum_mul]
        apply sum_congr rfl
        intro u hu
        rw [(mem_filter.mp hu).2]
      _ = _ := sum_fiberwise_of_maps_to
        (fun u _ => mem_image.mpr ⟨u, mem_univ _, rfl⟩) _
  simp_rw [← hF]
  rw [hf]
  simp only [wordEnergy, collision, F, mul_sum, sum_filter, mul_ite, mul_zero, f, W, eq_comm]

/-- The odd integer weights have absolute-sum threshold one. -/
theorem summable_oddWeight_iff (σ : ℝ) : Summable (oddWeight σ) ↔ 1 < σ := by
  constructor
  · intro hs
    by_contra hn
    exact not_summable_oddWeight (le_of_not_gt hn) hs
  · exact summable_oddWeight

private theorem oddWeight_sq (σ : ℝ) (j : ℕ) :
    oddWeight σ j ^ 2 = oddWeight (2*σ) j := by
  dsimp [oddWeight]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

/-- The initial odd coefficient vector has square-sum threshold one half. -/
theorem oddWeight_square_summable_iff (σ : ℝ) :
    Summable (fun j => oddWeight σ j ^ 2) ↔ 1/2 < σ := by
  simp_rw [oddWeight_sq]
  rw [summable_oddWeight_iff]
  constructor <;> intro h <;> linarith

/-- Throughout the strict half-strip, square summability coexists with failure of every uniform exponential power bound. -/
theorem half_strip_power_failure :
    ∀ σ : ℝ, σ ∈ Set.Ioc (1/2) 1 →
      Summable (fun j => oddWeight σ j ^ 2) ∧
      ¬(∃ C : ℝ, 0 ≤ C ∧ ∀ r k : ℕ, oddEnergy σ r k ≤ C^(2*k)) := by
  intro σ hσ
  refine ⟨(oddWeight_square_summable_iff σ).mpr hσ.1, ?_⟩
  rw [oddEnergy_uniform_exponential_bound_iff]
  exact not_lt_of_ge hσ.2


/-- The literal coefficients of `1-eta`, with the unit coefficient removed. -/
def replacementCoefficient (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else (-1 : ℝ)^n

/-- Each nonunit odd label has replacement coefficient minus one. -/
theorem replacementCoefficient_oddLabel (j : ℕ) :
    replacementCoefficient (2*j+3) = -1 := by
  have ho : Odd (2*j+3) := ⟨j+1, by omega⟩
  simp [replacementCoefficient, show ¬2*j+3 ≤ 1 by omega, ho.neg_one_pow]

/-- All words in nonunit odd labels have the same sign at a fixed depth. -/
theorem replacement_word_oddLabels {k r : ℕ} (u : Fin k → Fin r) :
    (∏ i, replacementCoefficient (2*(u i:ℕ)+3)) = (-1:ℝ)^k := by
  simp only [replacementCoefficient_oddLabel, prod_const, card_univ, Fintype.card_fin]

/-- Every contribution to an odd integer product has the common depth sign or is zero. -/
theorem replacement_word_odd_product_sign {k : ℕ} (n : Fin k → ℕ)
    (hn : Odd (∏ i, n i)) :
    0 ≤ (-1:ℝ)^k * ∏ i, replacementCoefficient (n i) := by
  have hterm (i : Fin k) : 0 ≤ -replacementCoefficient (n i) := by
    have ho := hn.of_dvd_nat (dvd_prod_of_mem n (mem_univ i))
    simp only [replacementCoefficient]
    split_ifs <;> simp [ho.neg_one_pow]
  have h := prod_nonneg (s := (univ : Finset (Fin k))) (fun i _ => hterm i)
  simpa only [prod_neg, card_univ, Fintype.card_fin] using h

end RHTower.OddDirichletPowerGrowth
