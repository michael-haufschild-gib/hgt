import GaloisForLFunctions.RHTower.CriticalDefectMeasure

/-!
# The positive coherent chart of the critical normal cone

`prime-valuation-dyadic-fermion-normal-cone-law`, equations `(13c)`–`(13f)`.

The critical coherent kernel is a genuine Gram kernel.  Put

`𝔥 = L²((0,1), dt/t)`,  `F_u(t) = e^{ut} - 1`,

so that `⟨F_u, F_v⟩ = ∫₀¹ (e^{ut}-1)(e^{vt}-1) dt/t` is finite (the integrand vanishes to first
order at the origin) and

`K(u,v) = exp(-½‖F_u - F_v‖²) = e^{-Φ(u)} e^{-Φ(v)} e^{⟨F_u,F_v⟩}`,  `Φ(u) = ½‖F_u‖²`.

This is the concrete form of the exponential-vector identity `⟨Exp F_u, Exp F_v⟩ = K(u,v)`: the
kernel is the exponential of a Gram matrix, damped by the diagonal, hence positive definite.
-/

open Filter Topology Set intervalIntegral MeasureTheory

namespace RHTower

noncomputable section

/-- The prime-scale inner product `⟨F_u, F_v⟩ = ∫₀¹ (e^{ut}-1)(e^{vt}-1) dt/t`. -/
def primeScaleInner (u v : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, divProfile (fun s => (Real.exp (u * s) - 1) * (Real.exp (v * s) - 1)) t

theorem divProfile_polarization (u v : ℝ) :
    divProfile (fun s => (Real.exp (u * s) - 1) * (Real.exp (v * s) - 1))
      = fun t => (divProfile (coherentProfile u 0) t + divProfile (coherentProfile v 0) t
          - divProfile (coherentProfile u v) t) / 2 := by
  funext t
  by_cases ht : t = 0
  · simp [divProfile, ht]
  · simp only [divProfile, if_neg ht, coherentProfile]
    rw [show (0 : ℝ) * t = 0 by ring, Real.exp_zero]
    field_simp
    ring

theorem continuousOn_divProfile_product (u v : ℝ) :
    ContinuousOn (divProfile (fun s => (Real.exp (u * s) - 1) * (Real.exp (v * s) - 1)))
      (Set.Icc 0 1) := by
  rw [divProfile_polarization]
  exact (((continuousOn_divProfile_coherentProfile u 0).add
    (continuousOn_divProfile_coherentProfile v 0)).sub
    (continuousOn_divProfile_coherentProfile u v)).div_const 2

theorem intervalIntegrable_divProfile_coherentProfile (u v : ℝ) :
    IntervalIntegrable (divProfile (coherentProfile u v)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  exact (continuousOn_divProfile_coherentProfile u v).integrableOn_compact isCompact_Icc

/-- **The polarization identity.**  The inner product is the Euclidean polarization of the coherent
exponent. -/
theorem primeScaleInner_eq (u v : ℝ) :
    primeScaleInner u v
      = coherentExponent u 0 + coherentExponent v 0 - coherentExponent u v := by
  rw [primeScaleInner, divProfile_polarization]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_divProfile_coherentProfile u 0).add
      (intervalIntegrable_divProfile_coherentProfile v 0))
    (intervalIntegrable_divProfile_coherentProfile u v)]
  rw [intervalIntegral.integral_add (intervalIntegrable_divProfile_coherentProfile u 0)
    (intervalIntegrable_divProfile_coherentProfile v 0)]
  rw [coherentExponent, coherentExponent, coherentExponent]
  ring

theorem coherentExponent_self (u : ℝ) : coherentExponent u u = 0 := by
  have h : divProfile (coherentProfile u u) = fun _ : ℝ => (0 : ℝ) := by
    funext t
    rw [divProfile, coherentProfile]
    split_ifs with ht
    · rfl
    · rw [sub_self]
      simp
  rw [coherentExponent, h]
  simp

/-- `‖F_u‖² = 2 Φ(u)`. -/
theorem primeScaleInner_self (u : ℝ) : primeScaleInner u u = 2 * coherentExponent u 0 := by
  rw [primeScaleInner_eq, coherentExponent_self]
  ring

/-- **`(13d)`: the coherent kernel is `exp(-½‖F_u - F_v‖²)`.** -/
theorem coherentKernel_eq_exp_neg_half_dist (u v : ℝ) :
    coherentKernel u v
      = Real.exp (-((primeScaleInner u u - 2 * primeScaleInner u v + primeScaleInner v v) / 2)) := by
  rw [coherentKernel, primeScaleInner_self, primeScaleInner_self, primeScaleInner_eq]
  congr 1
  ring

/-- **`(13e)`: the coherent kernel is the damped exponential of the Gram kernel.**  This is the
exponential-vector identity `⟨Exp F_u, Exp F_v⟩ = K(u,v)` written out. -/
theorem coherentKernel_eq_exp_inner (u v : ℝ) :
    coherentKernel u v
      = Real.exp (-coherentExponent u 0) * Real.exp (-coherentExponent v 0)
        * Real.exp (primeScaleInner u v) := by
  rw [coherentKernel, primeScaleInner_eq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-! ## Positive definiteness of the coherent chart -/

theorem primeScaleInner_comm (u v : ℝ) : primeScaleInner u v = primeScaleInner v u := by
  rw [primeScaleInner_eq, primeScaleInner_eq]
  have : coherentExponent u v = coherentExponent v u := by
    rw [coherentExponent, coherentExponent]
    congr 2
    funext t
    rw [divProfile, divProfile, coherentProfile, coherentProfile]
    split_ifs with ht
    · rfl
    · rw [show (Real.exp (u * t) - Real.exp (v * t)) ^ (2 : ℕ)
        = (Real.exp (v * t) - Real.exp (u * t)) ^ (2 : ℕ) by ring]
  rw [this]
  ring

theorem intervalIntegrable_divProfile_product (u v : ℝ) :
    IntervalIntegrable
      (divProfile (fun s => (Real.exp (u * s) - 1) * (Real.exp (v * s) - 1))) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  exact (continuousOn_divProfile_product u v).integrableOn_compact isCompact_Icc

/-- **The Gram kernel of the coherent chart is positive semidefinite.** -/
theorem primeScaleInner_quadForm_nonneg {n : ℕ} (u c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * primeScaleInner (u i) (u j) * c j := by
  have hint : ∀ i j : Fin n, IntervalIntegrable
      (fun t => c i * c j *
        divProfile (fun s => (Real.exp (u i * s) - 1) * (Real.exp (u j * s) - 1)) t)
      volume 0 1 := fun i j => (intervalIntegrable_divProfile_product (u i) (u j)).const_mul _
  set F : Fin n → ℝ → ℝ := fun i t => ∑ j, c i * c j *
    divProfile (fun s => (Real.exp (u i * s) - 1) * (Real.exp (u j * s) - 1)) t with hF
  have hFint : ∀ i, IntervalIntegrable (F i) volume 0 1 := by
    intro i
    have h := IntervalIntegrable.sum (Finset.univ : Finset (Fin n)) (fun j _ => hint i j)
    have heq : (∑ j ∈ (Finset.univ : Finset (Fin n)), fun t : ℝ => c i * c j *
        divProfile (fun s => (Real.exp (u i * s) - 1) * (Real.exp (u j * s) - 1)) t) = F i := by
      funext t
      rw [hF]
      simp
    rwa [heq] at h
  have hstep : ∀ i : Fin n, (∑ j, c i * primeScaleInner (u i) (u j) * c j)
      = ∫ t in (0 : ℝ)..1, F i t := by
    intro i
    rw [hF]
    simp only
    rw [intervalIntegral.integral_finsetSum (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul, primeScaleInner]
    ring
  have htot : (∫ t in (0 : ℝ)..1, ∑ i, F i t) = ∑ i, ∫ t in (0 : ℝ)..1, F i t :=
    intervalIntegral.integral_finsetSum (fun i _ => hFint i)
  have hswap : (∑ i, ∑ j, c i * primeScaleInner (u i) (u j) * c j)
      = ∫ t in (0 : ℝ)..1,
          divProfile (fun s => (∑ i, c i * (Real.exp (u i * s) - 1)) ^ (2 : ℕ)) t := by
    rw [Finset.sum_congr rfl fun i _ => hstep i, ← htot]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hF]
    simp only
    by_cases ht : t = 0
    · simp [divProfile, ht]
    · simp only [divProfile, if_neg ht]
      rw [sq, Finset.sum_mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
  rw [hswap]
  refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
  rw [divProfile]
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (sq_nonneg _) ht.1

/-! ## The coherent kernel is positive definite -/

theorem quadForm_of_posSemidef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef)
    (x : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, x i * M i j * x j := by
  have h := hM.dotProduct_mulVec_nonneg x
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using h

theorem posSemidef_of_quadForm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : ∀ i j, M i j = M j i)
    (h : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, x i * M i j * x j) : M.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact (hsymm j i)
  · intro x
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using h x

/-- The Gram matrix of the coherent chart. -/
def coherentGram {n : ℕ} (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => primeScaleInner (u i) (u j)

theorem coherentGram_posSemidef {n : ℕ} (u : Fin n → ℝ) : (coherentGram u).PosSemidef :=
  posSemidef_of_quadForm (fun i j => primeScaleInner_comm (u i) (u j))
    (fun x => primeScaleInner_quadForm_nonneg u x)

/-- **Hadamard powers of a positive semidefinite matrix are positive semidefinite.** -/
theorem hadamardPow_posSemidef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) :
    ∀ k : ℕ, (Matrix.of fun i j => (M i j) ^ k).PosSemidef := by
  intro k
  induction k with
  | zero =>
      refine posSemidef_of_quadForm (fun _ _ => by simp) (fun x => ?_)
      have : ∑ i, ∑ j, x i * (Matrix.of (fun (i j : Fin n) => (M i j) ^ (0 : ℕ))) i j * x j
          = (∑ i, x i) ^ (2 : ℕ) := by
        simp only [Matrix.of_apply, pow_zero, mul_one]
        rw [sq, Finset.sum_mul_sum]
      rw [this]
      exact sq_nonneg _
  | succ k ih =>
      have hh := hM.hadamard ih
      have heq : M.hadamard (Matrix.of fun i j => (M i j) ^ k)
          = Matrix.of fun i j => (M i j) ^ (k + 1) := by
        ext i j
        simp [Matrix.hadamard, pow_succ]
        ring
      rwa [heq] at hh

/-- **`(13e)`: the coherent kernel is a positive-definite Gram kernel.**  Every finite coherent
packet has nonnegative energy, so the chart `u ↦ Exp(F_u)` is a genuine Hilbert realization. -/
theorem coherentKernel_quadForm_nonneg {n : ℕ} (u c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * coherentKernel (u i) (u j) * c j := by
  set b : Fin n → ℝ := fun i => c i * Real.exp (-coherentExponent (u i) 0) with hb
  have hfac : ∀ i j, c i * coherentKernel (u i) (u j) * c j
      = b i * Real.exp (coherentGram u i j) * b j := by
    intro i j
    rw [coherentKernel_eq_exp_inner, hb, coherentGram]
    simp only [Matrix.of_apply]
    ring
  have hsummand : ∀ i j : Fin n,
      Summable (fun k : ℕ => b i * ((coherentGram u i j) ^ k / (Nat.factorial k : ℝ)) * b j) := by
    intro i j
    have h := (Real.summable_pow_div_factorial (coherentGram u i j)).mul_left (b i)
    have h2 := h.mul_right (b j)
    exact h2
  have hexp : ∀ i j : Fin n, b i * Real.exp (coherentGram u i j) * b j
      = ∑' k : ℕ, b i * ((coherentGram u i j) ^ k / (Nat.factorial k : ℝ)) * b j := by
    intro i j
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [← tsum_mul_left, ← tsum_mul_right]
  have hQ : ∀ k : ℕ, 0 ≤ ∑ i, ∑ j, b i * ((coherentGram u i j) ^ k / (Nat.factorial k : ℝ)) * b j := by
    intro k
    have hpsd := hadamardPow_posSemidef (coherentGram_posSemidef u) k
    have hq := quadForm_of_posSemidef hpsd b
    have hfact : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hrw : ∑ i, ∑ j, b i * ((coherentGram u i j) ^ k / (Nat.factorial k : ℝ)) * b j
        = (∑ i, ∑ j, b i * (Matrix.of (fun (i j : Fin n) => (coherentGram u i j) ^ k)) i j * b j)
          / (Nat.factorial k : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.of_apply]
      ring
    rw [hrw]
    exact div_nonneg hq hfact.le
  have hinner : ∀ i j : Fin n,
      HasSum (fun k : ℕ => b i * ((coherentGram u i j) ^ k / (Nat.factorial k : ℝ)) * b j)
        (b i * Real.exp (coherentGram u i j) * b j) := by
    intro i j
    rw [hexp i j]
    exact (hsummand i j).hasSum
  have hrow : ∀ i : Fin n,
      HasSum (fun k : ℕ => ∑ j, b i * ((coherentGram u i j) ^ k / (Nat.factorial k : ℝ)) * b j)
        (∑ j, b i * Real.exp (coherentGram u i j) * b j) :=
    fun i => hasSum_sum (fun j _ => hinner i j)
  have htotal : HasSum
      (fun k : ℕ => ∑ i, ∑ j, b i * ((coherentGram u i j) ^ k / (Nat.factorial k : ℝ)) * b j)
      (∑ i, ∑ j, b i * Real.exp (coherentGram u i j) * b j) :=
    hasSum_sum (fun i _ => hrow i)
  have hmain : ∑ i, ∑ j, c i * coherentKernel (u i) (u j) * c j
      = ∑' k : ℕ, ∑ i, ∑ j, b i * ((coherentGram u i j) ^ k / (Nat.factorial k : ℝ)) * b j := by
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hfac i j]
    exact htotal.tsum_eq.symm
  rw [hmain]
  exact tsum_nonneg hQ

end

end RHTower
