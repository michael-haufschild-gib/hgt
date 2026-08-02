import GaloisForLFunctions.RHTower.DeningerCapDerivBound

/-!
# The dilation expansion of a weighted derivative

The operator `U_n : f ↦ x^n f^{(n)}` satisfies `U_{n+1} = θU_n − nU_n` for the Euler operator
`θ = x d/dx`, so `U_n` is the falling factorial `θ(θ−1)⋯(θ−n+1)` — a linear combination of the
iterates of `θ` with the signed Stirling numbers of the first kind as coefficients.

Away from the origin this converts derivative seminorms into supremum seminorms of the Euler
iterates, which for a member of Meyer's space are controlled by the radial data of its Poisson sum.

* `deningerWeightedDerivCLM` : the operator `f ↦ x^n f^{(n)}`.
* `deningerWeightedDerivCLM_succ_apply` : **the recursion `U_{n+1} = θU_n − nU_n`.**
* `deningerWeightedDerivCLM_eq_sum` : **the expansion in the Euler iterates.**
* `seminorm_le_weightedDeriv` : `p_{k,n}(f) ≤ p_{0,n}(f) + p_{k,0}(U_n f)`.
-/

open scoped Real SchwartzMap FourierTransform ContDiff NNReal
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The weighted derivative -/

/-- The operator `f ↦ x^n f^{(n)}`. -/
def deningerWeightedDerivCLM : ℕ → (𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))
  | 0 => ContinuousLinearMap.id ℂ _
  | (n + 1) => (mulXCLM.comp (deningerWeightedDerivCLM n)).comp derivSCLM

theorem deningerWeightedDerivCLM_apply (n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deningerWeightedDerivCLM n f x = (x : ℂ) ^ n * ((derivSCLM^[n]) f) x := by
  induction n generalizing f with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, one_mul]
    rfl
  | succ n ih =>
    show mulXCLM (deningerWeightedDerivCLM n (derivSCLM f)) x = _
    rw [mulXCLM_apply, ih (derivSCLM f), Function.iterate_succ_apply, pow_succ]
    ring

theorem norm_deningerWeightedDerivCLM_apply (n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖deningerWeightedDerivCLM n f x‖ = |x| ^ n * ‖((derivSCLM^[n]) f) x‖ := by
  rw [deningerWeightedDerivCLM_apply, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- **The recursion `U_{n+1} = θU_n − nU_n`.** -/
theorem deningerWeightedDerivCLM_succ_apply (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    deningerWeightedDerivCLM (n + 1) f
      = eulerSCLM (deningerWeightedDerivCLM n f)
        - (n : ℂ) • deningerWeightedDerivCLM n f := by
  refine SchwartzMap.ext fun x => ?_
  set g : 𝓢(ℝ, ℂ) := (derivSCLM^[n]) f with hg
  have hgderiv : HasDerivAt ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (((derivSCLM^[n + 1]) f) x) x := by
    have hval : deriv ((g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = ((derivSCLM^[n + 1]) f) x := by
      rw [Function.iterate_succ_apply', hg, derivSCLM_apply]
    rw [← hval]
    exact g.hasDerivAt x
  have hz : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    have hreal : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    exact hreal.ofReal_comp.congr_deriv (by norm_num)
  have hpow : HasDerivAt (fun y : ℝ => (y : ℂ) ^ n) ((n : ℂ) * (x : ℂ) ^ (n - 1) * 1) x :=
    hz.pow n
  have hprod := hpow.mul hgderiv
  have hfun : ((deningerWeightedDerivCLM n f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun y : ℝ => (y : ℂ) ^ n * (g : ℝ → ℂ) y := by
    funext y
    rw [deningerWeightedDerivCLM_apply, hg]
  have hderiv : deriv ((deningerWeightedDerivCLM n f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x
      = (n : ℂ) * (x : ℂ) ^ (n - 1) * 1 * (g : ℝ → ℂ) x
        + (x : ℂ) ^ n * ((derivSCLM^[n + 1]) f) x := by
    rw [hfun]
    exact hprod.deriv
  have hxpow : (x : ℂ) * ((n : ℂ) * (x : ℂ) ^ (n - 1) * 1) = (n : ℂ) * (x : ℂ) ^ n := by
    rcases n with _ | m
    · simp
    · rw [Nat.add_sub_cancel]
      push_cast
      ring
  show deningerWeightedDerivCLM (n + 1) f x
      = eulerSCLM (deningerWeightedDerivCLM n f) x
        - ((n : ℂ) • deningerWeightedDerivCLM n f) x
  rw [eulerSCLM_apply, _root_.smul_apply, smul_eq_mul, hderiv,
    deningerWeightedDerivCLM_apply, deningerWeightedDerivCLM_apply,
    Function.iterate_succ_apply, pow_succ]
  have hgval : ((derivSCLM^[n]) (derivSCLM f)) x = ((derivSCLM^[n + 1]) f) x := by
    rw [Function.iterate_succ_apply]
  rw [hgval]
  have hgcoe : (g : ℝ → ℂ) x = ((derivSCLM^[n]) f) x := rfl
  rw [hgcoe]
  linear_combination (-(((derivSCLM^[n]) f) x)) * hxpow

/-! ## The Stirling coefficients -/

/-- The signed Stirling numbers of the first kind, as the coefficients of the falling factorial
`θ(θ−1)⋯(θ−n+1)`. -/
def deningerStirling : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => -(n : ℂ) * deningerStirling n 0
  | n + 1, j + 1 => deningerStirling n j - (n : ℂ) * deningerStirling n (j + 1)

theorem deningerStirling_eq_zero : ∀ {n j : ℕ}, n < j → deningerStirling n j = 0 := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rfl
  | succ n ih =>
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h1 : n < i := by omega
    have h2 : n < i + 1 := by omega
    show deningerStirling n i - (n : ℂ) * deningerStirling n (i + 1) = 0
    rw [ih h1, ih h2]
    ring

/-- **The weighted derivative is a combination of the Euler iterates.** -/
theorem deningerWeightedDerivCLM_eq_sum (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    deningerWeightedDerivCLM n f
      = ∑ j ∈ Finset.range (n + 1), deningerStirling n j • ((eulerSCLM^[j]) f) := by
  induction n generalizing f with
  | zero =>
    rw [Finset.sum_range_one, Function.iterate_zero_apply]
    show ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) f = deningerStirling 0 0 • f
    have hone : deningerStirling 0 0 = 1 := rfl
    rw [hone, one_smul]
    rfl
  | succ n ih =>
    rw [deningerWeightedDerivCLM_succ_apply, ih f, map_sum]
    have hterm : ∀ j : ℕ, eulerSCLM (deningerStirling n j • ((eulerSCLM^[j]) f))
        = deningerStirling n j • ((eulerSCLM^[j + 1]) f) := by
      intro j
      rw [map_smul, Function.iterate_succ_apply']
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    have hshift : (∑ j ∈ Finset.range (n + 1), deningerStirling n j • ((eulerSCLM^[j]) f))
        = (∑ i ∈ Finset.range n, deningerStirling n (i + 1) • ((eulerSCLM^[i + 1]) f))
          + deningerStirling n 0 • f := by
      have h := Finset.sum_range_succ' (fun j => deningerStirling n j • ((eulerSCLM^[j]) f)) n
      rw [h, Function.iterate_zero_apply]
    have hvanish : (∑ i ∈ Finset.range (n + 1),
          deningerStirling n (i + 1) • ((eulerSCLM^[i + 1]) f))
        = ∑ i ∈ Finset.range n, deningerStirling n (i + 1) • ((eulerSCLM^[i + 1]) f) := by
      rw [Finset.sum_range_succ, deningerStirling_eq_zero (Nat.lt_succ_self n), zero_smul,
        add_zero]
    have hrhs : (∑ j ∈ Finset.range (n + 1 + 1), deningerStirling (n + 1) j • ((eulerSCLM^[j]) f))
        = (∑ i ∈ Finset.range (n + 1),
            deningerStirling (n + 1) (i + 1) • ((eulerSCLM^[i + 1]) f))
          + deningerStirling (n + 1) 0 • f := by
      have h := Finset.sum_range_succ'
        (fun j => deningerStirling (n + 1) j • ((eulerSCLM^[j]) f)) (n + 1)
      rw [h, Function.iterate_zero_apply]
    have hcoeff : ∀ i : ℕ, deningerStirling (n + 1) (i + 1)
        = deningerStirling n i - (n : ℂ) * deningerStirling n (i + 1) := fun _ => rfl
    have hzero : deningerStirling (n + 1) 0 = -(n : ℂ) * deningerStirling n 0 := rfl
    rw [hrhs, hzero, hshift]
    have hsplit : (∑ i ∈ Finset.range (n + 1),
          deningerStirling (n + 1) (i + 1) • ((eulerSCLM^[i + 1]) f))
        = (∑ i ∈ Finset.range (n + 1), deningerStirling n i • ((eulerSCLM^[i + 1]) f))
          - (n : ℂ) • ∑ i ∈ Finset.range (n + 1),
              deningerStirling n (i + 1) • ((eulerSCLM^[i + 1]) f) := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoeff i, sub_smul, smul_smul]
    rw [hsplit, hvanish, smul_add, smul_smul, neg_mul, neg_smul]
    abel

/-! ## From derivative seminorms to weighted seminorms -/

/-- Away from the origin the weighted derivative dominates; at the origin the derivative supremum
does. -/
theorem seminorm_le_weightedDeriv (k n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    SchwartzMap.seminorm ℂ k n f
      ≤ SchwartzMap.seminorm ℂ 0 n f
        + SchwartzMap.seminorm ℂ k 0 (deningerWeightedDerivCLM n f) := by
  have h1 : 0 ≤ SchwartzMap.seminorm ℂ 0 n f := apply_nonneg _ _
  have h2 : 0 ≤ SchwartzMap.seminorm ℂ k 0 (deningerWeightedDerivCLM n f) := apply_nonneg _ _
  refine SchwartzMap.seminorm_le_bound' ℂ k n f (by linarith) fun x => ?_
  have hcoe : iteratedDeriv n ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = ((derivSCLM^[n]) f) x := by
    rw [coe_derivSCLM_iterate]
  rw [hcoe]
  rcases le_or_gt |x| 1 with hle | hgt
  · have hpow : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) hle
    have hbase : ‖((derivSCLM^[n]) f) x‖ ≤ SchwartzMap.seminorm ℂ 0 n f := by
      have h := SchwartzMap.le_seminorm' ℂ 0 n f x
      rw [pow_zero, one_mul, hcoe] at h
      exact h
    have hstep : |x| ^ k * ‖((derivSCLM^[n]) f) x‖ ≤ ‖((derivSCLM^[n]) f) x‖ := by
      nlinarith [norm_nonneg (((derivSCLM^[n]) f) x)]
    linarith
  · have hone : (1 : ℝ) ≤ |x| ^ n := one_le_pow₀ hgt.le
    have hnn : 0 ≤ ‖((derivSCLM^[n]) f) x‖ := norm_nonneg _
    have hgrow : ‖((derivSCLM^[n]) f) x‖ ≤ |x| ^ n * ‖((derivSCLM^[n]) f) x‖ := by
      nlinarith
    have hweighted : |x| ^ k * (|x| ^ n * ‖((derivSCLM^[n]) f) x‖)
        ≤ SchwartzMap.seminorm ℂ k 0 (deningerWeightedDerivCLM n f) := by
      have h := SchwartzMap.norm_pow_mul_le_seminorm ℂ (deningerWeightedDerivCLM n f) k x
      rw [Real.norm_eq_abs, norm_deningerWeightedDerivCLM_apply] at h
      calc |x| ^ k * (|x| ^ n * ‖((derivSCLM^[n]) f) x‖)
          = |x| ^ k * (|x| ^ n * ‖((derivSCLM^[n]) f) x‖) := rfl
        _ ≤ SchwartzMap.seminorm ℂ k 0 (deningerWeightedDerivCLM n f) := h
    have hkpos : (0 : ℝ) ≤ |x| ^ k := pow_nonneg (abs_nonneg x) k
    have hstep : |x| ^ k * ‖((derivSCLM^[n]) f) x‖
        ≤ |x| ^ k * (|x| ^ n * ‖((derivSCLM^[n]) f) x‖) :=
      mul_le_mul_of_nonneg_left hgrow hkpos
    linarith

/-! ## The seminorm of a combination -/

theorem seminorm_sum_le {ι : Type*} (p : Seminorm ℂ 𝓢(ℝ, ℂ)) (s : Finset ι)
    (g : ι → 𝓢(ℝ, ℂ)) : p (∑ i ∈ s, g i) ≤ ∑ i ∈ s, p (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (map_add_le_add p _ _) (by linarith [ih])

/-- **The supremum seminorms of a weighted derivative are bounded by those of the Euler
iterates.** -/
theorem seminorm_weightedDeriv_le_euler (n k : ℕ) (f : 𝓢(ℝ, ℂ)) :
    SchwartzMap.seminorm ℂ k 0 (deningerWeightedDerivCLM n f)
      ≤ ∑ j ∈ Finset.range (n + 1),
          ‖deningerStirling n j‖ * SchwartzMap.seminorm ℂ k 0 ((eulerSCLM^[j]) f) := by
  rw [deningerWeightedDerivCLM_eq_sum]
  refine le_trans (seminorm_sum_le (SchwartzMap.seminorm ℂ k 0) _ _) (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  exact map_smul_eq_mul (SchwartzMap.seminorm ℂ k 0) _ _

end RHTower

end
