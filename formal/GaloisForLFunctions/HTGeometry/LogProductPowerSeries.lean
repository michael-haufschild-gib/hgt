import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Normed
import GaloisForLFunctions.HTGeometry.CofinalSubsetTsum

/-!
# The logarithmic jets of a normally convergent linear product

For a family `a : ι → ℂ` with summable norms bounded by one and `‖t‖ < 1`, the sum of the
logarithms of the linear factors `1 - t·aᵢ` is the power series in `t` whose coefficients are the
power sums of the family.  Pairing the two orientations `±t` splits the jets by parity: the
intensity keeps exactly the even power sums, and the tangent-normalized phase keeps exactly the odd
power sums from the third on.

* `HTGeometry.hasSum_tsum_log_one_sub_mul`;
* `HTGeometry.hasSum_logIntensity`, `HTGeometry.hasSum_logPolarizedPhase`;
* `HTGeometry.hasDerivAt_logPhase_zero`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace HTGeometry

variable {ι : Type*} {a : ι → ℂ}

/-- The `k`-th power sum of a family. -/
def powerSum (a : ι → ℂ) (k : ℕ) : ℂ := ∑' i, (a i) ^ k

theorem summable_norm_pow (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1) {k : ℕ}
    (hk : 1 ≤ k) : Summable fun i => ‖(a i) ^ k‖ := by
  refine ha.of_nonneg_of_le (fun _ => norm_nonneg _) fun i => ?_
  rw [norm_pow]
  calc ‖a i‖ ^ k ≤ ‖a i‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (hb i) hk
    _ = ‖a i‖ := pow_one _

/-- The double family whose sum is the logarithm of the product. -/
def logTerm (a : ι → ℂ) (t : ℂ) (q : ι × ℕ) : ℂ := (t * a q.1) ^ q.2 / (q.2 : ℂ)

theorem summable_logTerm (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1) {t : ℂ}
    (ht : ‖t‖ < 1) : Summable fun q : ι × ℕ => ‖logTerm a t q‖ := by
  have hbound : ∀ q : ι × ℕ, ‖logTerm a t q‖ ≤ ‖a q.1‖ * ‖t‖ ^ q.2 := by
    rintro ⟨i, k⟩
    show ‖(t * a i) ^ k / (k : ℂ)‖ ≤ ‖a i‖ * ‖t‖ ^ k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hnorm : ‖(t * a i) ^ k / (k : ℂ)‖ = (‖t‖ ^ k * ‖a i‖ ^ k) / (k : ℝ) := by
      rw [norm_div, norm_pow, norm_mul, mul_pow, Complex.norm_natCast]
    rw [hnorm]
    have h1 : ‖a i‖ ^ k ≤ ‖a i‖ := by
      calc ‖a i‖ ^ k ≤ ‖a i‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) (hb i) hk
        _ = ‖a i‖ := pow_one _
    have hnn : (0 : ℝ) ≤ ‖t‖ ^ k * ‖a i‖ ^ k := by positivity
    calc (‖t‖ ^ k * ‖a i‖ ^ k) / (k : ℝ) ≤ ‖t‖ ^ k * ‖a i‖ ^ k := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
      _ ≤ ‖t‖ ^ k * ‖a i‖ := by gcongr
      _ = ‖a i‖ * ‖t‖ ^ k := by ring
  have hprod : Summable fun q : ι × ℕ => ‖a q.1‖ * ‖t‖ ^ q.2 :=
    ha.mul_of_nonneg (summable_geometric_of_lt_one (norm_nonneg t) ht)
      (fun _ => norm_nonneg _) (fun _ => by positivity)
  exact hprod.of_nonneg_of_le (fun _ => norm_nonneg _) hbound

set_option maxHeartbeats 1000000 in
theorem hasSum_powerSum_fiber (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1) (t : ℂ)
    (k : ℕ) : HasSum (fun i => logTerm a t (i, k)) (powerSum a k * t ^ k / (k : ℂ)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [logTerm]
  · have hsummable : Summable fun i => (a i) ^ k :=
      Summable.of_norm (summable_norm_pow ha hb hk)
    have hps : powerSum a k = ∑' i, (a i) ^ k := rfl
    have hmul : HasSum (fun i => (t ^ k / (k : ℂ)) * (a i) ^ k)
        ((t ^ k / (k : ℂ)) * powerSum a k) := by
      rw [hps]
      exact hsummable.hasSum.mul_left _
    have hfun : (fun i => (t ^ k / (k : ℂ)) * (a i) ^ k) = fun i => logTerm a t (i, k) := by
      funext i
      rw [logTerm, mul_pow]
      ring
    have hval : (t ^ k / (k : ℂ)) * powerSum a k = powerSum a k * t ^ k / (k : ℂ) := by ring
    rw [hfun, hval] at hmul
    exact hmul

set_option maxHeartbeats 1000000 in
/-- **The logarithmic power series of a normally convergent linear product.** -/
theorem hasSum_tsum_log_one_sub_mul (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1)
    {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun k : ℕ => -(powerSum a k * t ^ k / (k : ℂ)))
      (∑' i, Complex.log (1 - t * a i)) := by
  have hsum : Summable (logTerm a t) := Summable.of_norm (summable_logTerm ha hb ht)
  have hfib_i : ∀ i, HasSum (fun k : ℕ => logTerm a t (i, k))
      (-Complex.log (1 - t * a i)) := by
    intro i
    have hz : ‖t * a i‖ < 1 := by
      rw [norm_mul]
      calc ‖t‖ * ‖a i‖ ≤ ‖t‖ * 1 := by
            gcongr
            exact hb i
        _ = ‖t‖ := mul_one _
        _ < 1 := ht
    exact Complex.hasSum_taylorSeries_neg_log hz
  have htot : HasSum (fun i => -Complex.log (1 - t * a i)) (∑' q, logTerm a t q) :=
    hsum.hasSum.prod_fiberwise hfib_i
  have hswap : Summable fun q : ℕ × ι => logTerm a t (q.2, q.1) := hsum.prod_symm
  have hk : HasSum (fun k : ℕ => powerSum a k * t ^ k / (k : ℂ)) (∑' q, logTerm a t q) := by
    have hval : (∑' q : ℕ × ι, logTerm a t (q.2, q.1)) = ∑' q, logTerm a t q :=
      (Equiv.prodComm ℕ ι).tsum_eq (logTerm a t)
    rw [← hval]
    exact hswap.hasSum.prod_fiberwise fun k => hasSum_powerSum_fiber ha hb t k
  have hneg : (∑' i, Complex.log (1 - t * a i)) = -∑' q, logTerm a t q := by
    have := htot.tsum_eq
    rw [tsum_neg] at this
    linear_combination -this
  rw [hneg]
  exact hk.neg

set_option maxHeartbeats 1000000 in
/-- **The even jet split.**  The logarithm of the intensity keeps exactly the even power sums. -/
theorem hasSum_logIntensity (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1)
    {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun j : ℕ => -(powerSum a (2 * (j + 1)) * t ^ (2 * (j + 1)) / ((j : ℂ) + 1)))
      ((∑' i, Complex.log (1 - t * a i)) + ∑' i, Complex.log (1 + t * a i)) := by
  have hneg : ‖-t‖ < 1 := by rwa [norm_neg]
  have h₁ := hasSum_tsum_log_one_sub_mul ha hb ht
  have h₂ := hasSum_tsum_log_one_sub_mul ha hb hneg
  have hrw : (∑' i, Complex.log (1 - (-t) * a i)) = ∑' i, Complex.log (1 + t * a i) := by
    refine tsum_congr fun i => ?_
    congr 1
    ring
  rw [hrw] at h₂
  set F : ℕ → ℂ := fun k =>
    -(powerSum a k * t ^ k / (k : ℂ)) + -(powerSum a k * (-t) ^ k / (k : ℂ)) with hF
  have hstep : HasSum F
      ((∑' i, Complex.log (1 - t * a i)) + ∑' i, Complex.log (1 + t * a i)) := h₁.add h₂
  have hinj : Function.Injective fun j : ℕ => 2 * (j + 1) := by
    intro x y hxy
    dsimp only at hxy
    omega
  have hout : ∀ k : ℕ, k ∉ Set.range (fun j : ℕ => 2 * (j + 1)) → F k = 0 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp [hF]
    · have hodd : ¬ (2 ∣ k) := by
        rintro ⟨m, hm⟩
        refine hk ⟨m - 1, ?_⟩
        dsimp only
        omega
      have hpow : (-t) ^ k = -(t ^ k) := Odd.neg_pow (Nat.odd_iff.mpr (by omega)) t
      rw [hF]
      simp only [hpow]
      ring
  have hbase : HasSum (F ∘ fun j : ℕ => 2 * (j + 1))
      ((∑' i, Complex.log (1 - t * a i)) + ∑' i, Complex.log (1 + t * a i)) :=
    (Function.Injective.hasSum_iff hinj hout).mpr hstep
  have hfun : (fun j : ℕ => -(powerSum a (2 * (j + 1)) * t ^ (2 * (j + 1)) / ((j : ℂ) + 1)))
      = F ∘ fun j : ℕ => 2 * (j + 1) := by
    funext j
    have h2 : ((2 * (j + 1) : ℕ) : ℂ) = 2 * ((j : ℂ) + 1) := by push_cast; ring
    have hpow : (-t) ^ (2 * (j + 1)) = t ^ (2 * (j + 1)) := Even.neg_pow ⟨j + 1, by ring⟩ t
    have hne : ((j : ℂ) + 1) ≠ 0 := by
      intro hcon
      have hre := congrArg Complex.re hcon
      simp at hre
      have : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      linarith
    show -(powerSum a (2 * (j + 1)) * t ^ (2 * (j + 1)) / ((j : ℂ) + 1)) = F (2 * (j + 1))
    rw [hF]
    simp only [hpow, h2]
    field_simp
    ring
  rw [hfun]
  exact hbase

set_option maxHeartbeats 1000000 in
/-- **The odd jet split.**  After the unique linear counterterm, the logarithm of the polarized
phase keeps exactly the odd power sums from the third on. -/
theorem hasSum_logPolarizedPhase (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1)
    {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun j : ℕ => -(2 * powerSum a (2 * (j + 1) + 1) * t ^ (2 * (j + 1) + 1)
        / ((2 * (j + 1) + 1 : ℕ) : ℂ)))
      ((∑' i, Complex.log (1 - t * a i)) - (∑' i, Complex.log (1 + t * a i))
        + 2 * powerSum a 1 * t) := by
  have hneg : ‖-t‖ < 1 := by rwa [norm_neg]
  have h₁ := hasSum_tsum_log_one_sub_mul ha hb ht
  have h₂ := hasSum_tsum_log_one_sub_mul ha hb hneg
  have hrw : (∑' i, Complex.log (1 - (-t) * a i)) = ∑' i, Complex.log (1 + t * a i) := by
    refine tsum_congr fun i => ?_
    congr 1
    ring
  rw [hrw] at h₂
  set G : ℕ → ℂ := fun k =>
    -(powerSum a k * t ^ k / (k : ℂ)) - -(powerSum a k * (-t) ^ k / (k : ℂ)) with hG
  have hstep : HasSum G
      ((∑' i, Complex.log (1 - t * a i)) - ∑' i, Complex.log (1 + t * a i)) := h₁.sub h₂
  have hinj : Function.Injective fun j : ℕ => 2 * j + 1 := by
    intro x y hxy
    dsimp only at hxy
    omega
  have hout : ∀ k : ℕ, k ∉ Set.range (fun j : ℕ => 2 * j + 1) → G k = 0 := by
    intro k hk
    have heven : 2 ∣ k := by
      rcases Nat.even_or_odd k with he | ho
      · exact he.two_dvd
      · exfalso
        obtain ⟨m, hm⟩ := ho
        refine hk ⟨m, ?_⟩
        dsimp only
        omega
    obtain ⟨m, hm⟩ := heven
    have hpow : (-t) ^ k = t ^ k := by
      rw [hm]
      exact Even.neg_pow ⟨m, by ring⟩ t
    rw [hG]
    simp only [hpow]
    ring
  have hbase : HasSum (G ∘ fun j : ℕ => 2 * j + 1)
      ((∑' i, Complex.log (1 - t * a i)) - ∑' i, Complex.log (1 + t * a i)) :=
    (Function.Injective.hasSum_iff hinj hout).mpr hstep
  have hodd : ∀ j : ℕ, (G ∘ fun j : ℕ => 2 * j + 1) j
      = -(2 * powerSum a (2 * j + 1) * t ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℂ)) := by
    intro j
    have hpow : (-t) ^ (2 * j + 1) = -(t ^ (2 * j + 1)) :=
      Odd.neg_pow ⟨j, by ring⟩ t
    show G (2 * j + 1) = _
    rw [hG]
    simp only [hpow]
    ring
  have hshift : HasSum (fun n : ℕ => (G ∘ fun j : ℕ => 2 * j + 1) (n + 1))
      (((∑' i, Complex.log (1 - t * a i)) - ∑' i, Complex.log (1 + t * a i))
        - (G ∘ fun j : ℕ => 2 * j + 1) 0) := by
    refine (hasSum_nat_add_iff (f := G ∘ fun j : ℕ => 2 * j + 1) 1).mpr ?_
    simpa using hbase
  have hzero : (G ∘ fun j : ℕ => 2 * j + 1) 0 = -(2 * powerSum a 1 * t) := by
    rw [hodd 0]
    norm_num
  have hval : ((∑' i, Complex.log (1 - t * a i)) - ∑' i, Complex.log (1 + t * a i))
      - (G ∘ fun j : ℕ => 2 * j + 1) 0
      = (∑' i, Complex.log (1 - t * a i)) - (∑' i, Complex.log (1 + t * a i))
        + 2 * powerSum a 1 * t := by
    rw [hzero]
    ring
  have hfinal : HasSum (fun j : ℕ => (G ∘ fun j : ℕ => 2 * j + 1) (j + 1))
      ((∑' i, Complex.log (1 - t * a i)) - (∑' i, Complex.log (1 + t * a i))
        + 2 * powerSum a 1 * t) := by
    rw [← hval]
    exact hshift
  refine hfinal.congr_fun fun j => ?_
  rw [hodd (j + 1)]

/-- The logarithms of the linear factors are absolutely summable. -/
theorem summable_norm_log_one_sub_mul (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1)
    {t : ℂ} (ht : ‖t‖ < 1) : Summable fun i => ‖Complex.log (1 - t * a i)‖ := by
  have htpos : (0 : ℝ) < 1 - ‖t‖ := by linarith
  have hbound : ∀ i, ‖Complex.log (1 - t * a i)‖ ≤ ((1 - ‖t‖)⁻¹ / 2 + 1) * ‖a i‖ := by
    intro i
    have hx : ‖-(t * a i)‖ = ‖t‖ * ‖a i‖ := by rw [norm_neg, norm_mul]
    have hxt : ‖t‖ * ‖a i‖ ≤ ‖t‖ := by
      calc ‖t‖ * ‖a i‖ ≤ ‖t‖ * 1 := by
            gcongr
            exact hb i
        _ = ‖t‖ := mul_one _
    have hnorm : ‖-(t * a i)‖ < 1 := by
      rw [hx]
      linarith
    have hlog := Complex.norm_log_one_add_le hnorm
    have heq : (1 : ℂ) + -(t * a i) = 1 - t * a i := by ring
    rw [heq, hx] at hlog
    have hpos : (0 : ℝ) < 1 - ‖t‖ * ‖a i‖ := by linarith
    have hnn : (0 : ℝ) ≤ ‖a i‖ := norm_nonneg _
    have htn : (0 : ℝ) ≤ ‖t‖ := norm_nonneg _
    have hai1 : ‖a i‖ ≤ 1 := hb i
    have hinvle : (1 - ‖t‖ * ‖a i‖)⁻¹ ≤ (1 - ‖t‖)⁻¹ := by
      refine inv_anti₀ htpos ?_
      linarith
    have hTA : ‖t‖ * ‖a i‖ ≤ ‖a i‖ := by nlinarith [hnn, ht.le]
    have hsq : (‖t‖ * ‖a i‖) ^ 2 ≤ ‖a i‖ := by
      have h1 : (‖t‖ * ‖a i‖) ^ 2 ≤ ‖a i‖ ^ 2 := by
        refine pow_le_pow_left₀ (by positivity) hTA 2
      have h2 : ‖a i‖ ^ 2 ≤ ‖a i‖ := by nlinarith [hnn, hai1]
      linarith
    have hinvnn : (0 : ℝ) ≤ (1 - ‖t‖ * ‖a i‖)⁻¹ := by positivity
    have hkey : (‖t‖ * ‖a i‖) ^ 2 * (1 - ‖t‖ * ‖a i‖)⁻¹ ≤ ‖a i‖ * (1 - ‖t‖)⁻¹ :=
      le_trans (mul_le_mul_of_nonneg_right hsq hinvnn)
        (mul_le_mul_of_nonneg_left hinvle hnn)
    have hlin : ‖t‖ * ‖a i‖ ≤ ‖a i‖ := hTA
    have hfin : ‖a i‖ * (1 - ‖t‖)⁻¹ / 2 + ‖a i‖ = ((1 - ‖t‖)⁻¹ / 2 + 1) * ‖a i‖ := by ring
    linarith
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound ?_
  exact ha.mul_left _

/-- **Cofinal convergence of the logarithmic sums.**  Along any family of index subsets eventually
containing every finite set, the partial logarithmic sums converge to the total one. -/
theorem tendsto_tsum_log_of_cofinal {α : Type*} {l : Filter α} {A : α → Set ι}
    (ha : Summable fun i => ‖a i‖) (hb : ∀ i, ‖a i‖ ≤ 1) {t : ℂ} (ht : ‖t‖ < 1)
    (hcof : ∀ F : Finset ι, ∀ᶠ x in l, (F : Set ι) ⊆ A x) :
    Filter.Tendsto (fun x => ∑' i : (A x : Set ι), Complex.log (1 - t * a i)) l
      (nhds (∑' i, Complex.log (1 - t * a i))) :=
  tendsto_tsum_subtype_of_cofinal (summable_norm_log_one_sub_mul ha hb ht) hcof

end HTGeometry
