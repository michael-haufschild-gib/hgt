import GaloisForLFunctions.MultiplicativePositivityGeometry.ZetaBoundaryDivisor

/-!
# Arithmetic realization: twisting the von Mangoldt weights

For a nonnegative cosine polynomial `P(θ) = Σ_{k ≤ K} a_k cos(kθ)` and a height `t₀`, the weights
`Λ(n) n^{-1-x} P(t₀ log n)` are nonnegative. They are the log-derivative coefficients of
`Π_k (ζ(s + ikt₀) ζ(s − ikt₀))^{a_k/2}`. Since `cos(kt₀ log n) cos(u log n)` splits into two shifted
characters and `D_ζ = 1_{0}`, the boundary divisor is `Σ_k (a_k/2)(δ(u + kt₀) + δ(u − kt₀))`
(`twisted_isBoundaryDivisor`).

* On the progression `t₀ℤ` this divisor is `a₀` at `0` and `a_k/2` at `±kt₀`
  (`twistedDivisor_zero`, `twistedDivisor_mul`). Every nonnegative cosine polynomial is a boundary
  profile, and its coefficient profile is positive definite on `ℤ` (`twistedProfile_isEvenPosDef`).
* `P = 2 − 2cos θ` gives the boundary divisor of `ζ(s)²/(ζ(s+it₀)ζ(s−it₀))`: a double pole, simple
  boundary zeros at `±t₀`, no other boundary pole. Its zero mass on the progression `t₀, 2t₀, …` is
  `1 = D(0)/2`. So the progression law is sharp, and pole simplicity cannot be dropped from the
  boundary forcing law (`doublePoleProfile_progression_mass`, `doublePoleProfile_has_zero`).
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- Composition with an additive homomorphism preserves even positive definiteness. -/
theorem IsEvenPosDef.comp_addMonoidHom {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    {φ : G → ℝ} (hφ : IsEvenPosDef φ) (f : G' →+ G) : IsEvenPosDef (φ ∘ f) where
  even u := by simp [hφ.even]
  posDef n x c := by
    simpa [Function.comp, map_sub] using hφ.posDef n (fun i => f (x i)) c

/-- The point mass at the origin. -/
noncomputable def diracAt (v : ℝ) : ℝ := if v = 0 then 1 else 0

/-- Von Mangoldt weights twisted by the cosine polynomial `P(t₀ log n)`. -/
noncomputable def twistedWeight (a : ℕ → ℝ) (K : ℕ) (t₀ x : ℝ) (n : ℕ) : ℝ :=
  zetaBoundaryWeight x n * HTGeometry.cosinePolynomial a K (t₀ * logFrequency n)

/-- The boundary divisor of the twisted weights. -/
noncomputable def twistedDivisor (a : ℕ → ℝ) (K : ℕ) (t₀ u : ℝ) : ℝ :=
  ∑ k ∈ range (K + 1), a k / 2 * (diracAt (u + k * t₀) + diracAt (u - k * t₀))

theorem abs_cosinePolynomial_le (a : ℕ → ℝ) (K : ℕ) (θ : ℝ) :
    |HTGeometry.cosinePolynomial a K θ| ≤ ∑ k ∈ range (K + 1), |a k| := by
  unfold HTGeometry.cosinePolynomial
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- Product-to-sum for one twisted mode. -/
private theorem twist_mode (w L u t₀ ak : ℝ) (k : ℕ) :
    w * (ak * Real.cos (k * (t₀ * L))) * Real.cos (L * u) =
      ak / 2 * (w * Real.cos (L * (u + k * t₀)) + w * Real.cos (L * (u - k * t₀))) := by
  have h1 : L * (u + k * t₀) = L * u + k * (t₀ * L) := by ring
  have h2 : L * (u - k * t₀) = L * u - k * (t₀ * L) := by ring
  rw [h1, h2, Real.cos_add, Real.cos_sub]
  ring

/-- The twisted cosine trace is a finite combination of shifted ζ traces. -/
theorem cosineTrace_twistedWeight {a : ℕ → ℝ} {K : ℕ} {t₀ x : ℝ} (hx : 0 < x) (u : ℝ) :
    cosineTrace (twistedWeight a K t₀ x) logFrequency u =
      ∑ k ∈ range (K + 1), a k / 2 *
        (cosineTrace (zetaBoundaryWeight x) logFrequency (u + k * t₀) +
          cosineTrace (zetaBoundaryWeight x) logFrequency (u - k * t₀)) := by
  have hz := summable_zetaBoundaryWeight hx
  have hnn := zetaBoundaryWeight_nonneg x
  have hS : HasSum (fun n => ∑ k ∈ range (K + 1), a k / 2 *
        (zetaBoundaryWeight x n * Real.cos (logFrequency n * (u + k * t₀)) +
          zetaBoundaryWeight x n * Real.cos (logFrequency n * (u - k * t₀))))
      (∑ k ∈ range (K + 1), a k / 2 *
        (cosineTrace (zetaBoundaryWeight x) logFrequency (u + k * t₀) +
          cosineTrace (zetaBoundaryWeight x) logFrequency (u - k * t₀))) :=
    hasSum_sum fun k _ => (((summable_cosineTrace_terms hnn hz logFrequency _).hasSum).add
      ((summable_cosineTrace_terms hnn hz logFrequency _).hasSum)).mul_left _
  rw [← hS.tsum_eq]
  unfold cosineTrace
  refine tsum_congr fun n => ?_
  unfold twistedWeight HTGeometry.cosinePolynomial
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => twist_mode _ _ _ _ _ _

/-- **Arithmetic realization.** For a nonnegative cosine polynomial, the twisted von Mangoldt
weights form a boundary datum whose divisor is the shifted combination of point masses. -/
theorem twisted_isBoundaryDivisor {a : ℕ → ℝ} {K : ℕ}
    (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ) (t₀ : ℝ) :
    IsBoundaryDivisor logFrequency (twistedWeight a K t₀) (twistedDivisor a K t₀) where
  nonneg x _ n := mul_nonneg (zetaBoundaryWeight_nonneg x n) (hP _)
  summable x hx := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (zetaBoundaryWeight_nonneg x n) (hP _))
      (fun n => ?_) ((summable_zetaBoundaryWeight hx).mul_right (∑ k ∈ range (K + 1), |a k|))
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_cosinePolynomial_le a K _))
      (zetaBoundaryWeight_nonneg x n)
  tendsto u := by
    have hlim : Tendsto (fun x => ∑ k ∈ range (K + 1), a k / 2 *
          (x * cosineTrace (zetaBoundaryWeight x) logFrequency (u + k * t₀) +
            x * cosineTrace (zetaBoundaryWeight x) logFrequency (u - k * t₀)))
        (𝓝[>] 0) (𝓝 (twistedDivisor a K t₀ u)) := by
      have h : Tendsto (fun x => ∑ k ∈ range (K + 1), a k / 2 *
            (x * cosineTrace (zetaBoundaryWeight x) logFrequency (u + k * t₀) +
              x * cosineTrace (zetaBoundaryWeight x) logFrequency (u - k * t₀)))
          (𝓝[>] 0) (𝓝 (∑ k ∈ range (K + 1), a k / 2 *
            (zetaBoundaryDivisor (u + k * t₀) + zetaBoundaryDivisor (u - k * t₀)))) :=
        tendsto_finsetSum _ fun k _ =>
          ((zeta_isBoundaryDivisor.tendsto _).add (zeta_isBoundaryDivisor.tendsto _)).const_mul _
      simpa only [zetaBoundaryDivisor_eq, twistedDivisor, diracAt] using h
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [cosineTrace_twistedWeight (Set.mem_Ioi.mp hx), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem twistedDivisor_isEvenPosDef {a : ℕ → ℝ} {K : ℕ}
    (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ) (t₀ : ℝ) :
    IsEvenPosDef (twistedDivisor a K t₀) :=
  (twisted_isBoundaryDivisor hP t₀).isEvenPosDef

/-- Value at the origin: the constant coefficient. -/
theorem twistedDivisor_zero (a : ℕ → ℝ) (K : ℕ) {t₀ : ℝ} (ht₀ : t₀ ≠ 0) :
    twistedDivisor a K t₀ 0 = a 0 := by
  unfold twistedDivisor
  rw [Finset.sum_eq_single 0]
  · simp only [diracAt, Nat.cast_zero, zero_mul, add_zero, sub_zero, if_true]
    ring
  · intro k _ hk
    have hk' : (k : ℝ) * t₀ ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hk) ht₀
    simp [diracAt, hk']
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos K)) h

/-- Value at `m t₀`, `1 ≤ m ≤ K`: half the `m`-th coefficient. -/
theorem twistedDivisor_mul (a : ℕ → ℝ) {K m : ℕ} (hm : 1 ≤ m) (hmK : m ≤ K) {t₀ : ℝ}
    (ht₀ : t₀ ≠ 0) : twistedDivisor a K t₀ (m * t₀) = a m / 2 := by
  unfold twistedDivisor
  rw [Finset.sum_eq_single m]
  · have hpos : (m : ℝ) * t₀ + m * t₀ ≠ 0 := by
      rw [← two_mul]
      exact mul_ne_zero two_ne_zero (mul_ne_zero (by positivity) ht₀)
    simp [diracAt, hpos]
  · intro k _ hk
    have h1 : (m : ℝ) * t₀ + k * t₀ ≠ 0 := by
      rw [← add_mul]
      exact mul_ne_zero (by positivity) ht₀
    have h2 : (m : ℝ) * t₀ - k * t₀ ≠ 0 := by
      rw [← sub_mul]
      exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hk))) ht₀
    simp [diracAt, h1, h2]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hmK)) h

/-- Off the points `±k t₀` the twisted divisor vanishes. -/
theorem twistedDivisor_eq_zero (a : ℕ → ℝ) (K : ℕ) {t₀ u : ℝ}
    (hu : ∀ k ≤ K, u ≠ k * t₀ ∧ u ≠ -(k * t₀)) : twistedDivisor a K t₀ u = 0 := by
  unfold twistedDivisor
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' := hu k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have h1 : u + k * t₀ ≠ 0 := fun h => hk'.2 (by linarith)
  have h2 : u - k * t₀ ≠ 0 := fun h => hk'.1 (by linarith)
  simp [diracAt, h1, h2]

/-- The coefficient profile of a nonnegative cosine polynomial is positive definite on `ℤ`. -/
theorem twistedProfile_isEvenPosDef {a : ℕ → ℝ} {K : ℕ}
    (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ) (t₀ : ℝ) :
    IsEvenPosDef (fun m : ℤ => twistedDivisor a K t₀ (m * t₀)) := by
  exact (twistedDivisor_isEvenPosDef hP t₀).comp_addMonoidHom
    ((AddMonoidHom.mulRight t₀).comp (Int.castAddHom ℝ))

/-! ### The double-pole profile -/

/-- Coefficients of `2 − 2cos θ`. -/
def doublePoleCoeff : ℕ → ℝ
  | 0 => 2
  | 1 => -2
  | _ => 0

theorem doublePoleCoeff_nonneg_poly (θ : ℝ) :
    0 ≤ HTGeometry.cosinePolynomial doublePoleCoeff 1 θ := by
  simp only [HTGeometry.cosinePolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
    doublePoleCoeff]
  push_cast
  simp only [zero_mul, Real.cos_zero, one_mul]
  linarith [Real.cos_le_one θ]

/-- The boundary divisor of `ζ(s)²/(ζ(s+it₀)ζ(s−it₀))`. -/
noncomputable def doublePoleProfile (t₀ : ℝ) : ℝ → ℝ := twistedDivisor doublePoleCoeff 1 t₀

theorem doublePoleProfile_isBoundaryDivisor (t₀ : ℝ) :
    IsBoundaryDivisor logFrequency (twistedWeight doublePoleCoeff 1 t₀)
      (doublePoleProfile t₀) :=
  twisted_isBoundaryDivisor doublePoleCoeff_nonneg_poly t₀

theorem doublePoleProfile_zero {t₀ : ℝ} (ht₀ : t₀ ≠ 0) : doublePoleProfile t₀ 0 = 2 :=
  twistedDivisor_zero _ _ ht₀

/-- **A boundary zero beside a double pole.** -/
theorem doublePoleProfile_has_zero {t₀ : ℝ} (ht₀ : t₀ ≠ 0) : doublePoleProfile t₀ t₀ = -1 := by
  have := twistedDivisor_mul doublePoleCoeff (K := 1) (m := 1) le_rfl le_rfl ht₀
  simp only [Nat.cast_one, one_mul] at this
  rw [doublePoleProfile, this]
  simp [doublePoleCoeff]

/-- No boundary pole off the origin. -/
theorem doublePoleProfile_nonpos {t₀ u : ℝ} (ht₀ : t₀ ≠ 0) (hu : u ≠ 0) :
    doublePoleProfile t₀ u ≤ 0 := by
  by_cases h1 : u = t₀
  · rw [h1, doublePoleProfile_has_zero ht₀]; norm_num
  by_cases h2 : u = -t₀
  · rw [h2, doublePoleProfile, (twistedDivisor_isEvenPosDef doublePoleCoeff_nonneg_poly t₀).even]
    exact (doublePoleProfile_has_zero ht₀).le.trans (by norm_num)
  · rw [doublePoleProfile, twistedDivisor_eq_zero]
    intro k hk
    interval_cases k <;> simp [hu, h1, h2]

/-- **Sharpness of the progression law.** The double-pole profile has zero mass exactly
`D(0)/2 = 1` on the progression `t₀, 2t₀, 3t₀, …`. -/
theorem doublePoleProfile_progression_mass {t₀ : ℝ} (ht₀ : t₀ ≠ 0) {R : ℕ} (hR : 1 ≤ R) :
    ∑ r ∈ range R, -doublePoleProfile t₀ ((r + 1 : ℕ) * t₀) = doublePoleProfile t₀ 0 / 2 := by
  rw [doublePoleProfile_zero ht₀]
  obtain ⟨R, rfl⟩ := Nat.exists_eq_add_of_le' hR
  rw [Finset.sum_range_succ']
  have hrest : ∑ r ∈ range R, -doublePoleProfile t₀ ((r + 1 + 1 : ℕ) * t₀) = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [neg_eq_zero, doublePoleProfile, twistedDivisor_eq_zero]
    intro k hk
    have hne : ((r + 1 + 1 : ℕ) : ℝ) ≠ k := by
      have : k < r + 1 + 1 := by omega
      exact_mod_cast this.ne'
    refine ⟨fun h => hne (mul_right_cancel₀ ht₀ h), fun h => ?_⟩
    have : ((r + 1 + 1 : ℕ) : ℝ) * t₀ + k * t₀ = 0 := by linarith
    rw [← add_mul] at this
    exact (mul_ne_zero (by positivity) ht₀) this
  rw [hrest, zero_add]
  simp only [zero_add, Nat.cast_one, one_mul]
  rw [doublePoleProfile_has_zero ht₀]
  norm_num

end GaloisForLFunctions.MultiplicativePositivityGeometry
