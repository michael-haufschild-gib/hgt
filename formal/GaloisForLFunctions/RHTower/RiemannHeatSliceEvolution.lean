import GaloisForLFunctions.RHTower.DeBruijnLaguerreEvolution

/-!
# Evolution of every slice coefficient along the de Bruijn–Newman flow

Let `H_λ = riemannHeat λ` and `S_λ(t, x) = H_λ(t − ix) H_λ(t + ix)`, the horizontal slice of `H_λ` at
height `t`.  Write `D_n(λ, t) = ∂_x^n S_λ(t, ·)(0)` (`heatSliceTaylor`), so the slice coefficients
are `c_n = D_n/n!`.  Since `∂_λ H_λ = −∂_z² H_λ`, the slice obeys

  `∂_λ S = ½ (∂_x² − ∂_t²) S`:

forward heat in the slice variable `x`, backward heat in the height `t`.  On Taylor coefficients this
is the hierarchy (`hasDerivAt_heatSliceTaylor_time`)

  `∂_λ D_n = ½ (D_{n+2} − ∂_t² D_n)`,   i.e.   `∂_λ c_n = ½ (n+2)(n+1) c_{n+2} − ½ ∂_t² c_n`.

For `n = 2` this is the evolution law of the first Laguerre expression
(`hasDerivAt_laguerreExpr_time`, `∂_λ L = −∂_z² L + 2L₁`), since `c_2 = L` and
`6 c_4 = 2L₁ − ½ ∂_t² L`.

The two halves pull in opposite directions.  The term `D_{n+2}` couples each coefficient to the next
one with a positive weight, so forward time feeds positivity down the hierarchy: the operator
`e^{s∂_x²}` maps series with nonnegative coefficients to series with nonnegative coefficients.  The
height term is a backward heat operator, which is where the flow can create sign changes in `t`.

The proof expands `D_n` by Leibniz and the chain rule into
`Σ_k C(n,k) (−i)^k i^{n−k} H^{(k)}(t) H^{(n−k)}(t)` (`heatSliceTaylor_eq`), differentiates each term
in `λ` and in `t`, and computes `D_{n+2}` through `∂_x² S = −H''H + 2H'H' − HH''`.
-/

open Complex Filter Topology

namespace RHTower.DeBruijn

noncomputable section

/-- **Leibniz rule for a horizontal pair.**  For entire `A`, `B`,
`∂_x^n [A(t − ix) B(t + ix)](0) = Σ_k C(n,k) ((−i)^k A^{(k)}(t)) (i^{n−k} B^{(n−k)}(t))`. -/
theorem iteratedDeriv_slicePair {A B : ℂ → ℂ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (t : ℂ) (n : ℕ) :
    iteratedDeriv n (fun x => A (t - I * x) * B (t + I * x)) 0 =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
        ((-I) ^ k * iteratedDeriv k A t) * (I ^ (n - k) * iteratedDeriv (n - k) B t) := by
  have hcomp : ∀ (F : ℂ → ℂ), Differentiable ℂ F → ∀ (c : ℂ) (k : ℕ),
      iteratedDeriv k (fun x => F (t + c * x)) 0 = c ^ k * iteratedDeriv k F t := by
    intro F hF c k
    have hc : ContDiff ℂ k (fun z => F (t + z)) :=
      (hF.comp (differentiable_const t |>.add differentiable_id)).contDiff
    have h1 := congrFun (iteratedDeriv_comp_const_mul hc c) 0
    simp only [mul_zero] at h1
    rw [h1, iteratedDeriv_comp_const_add]
    simp only [add_zero]
  have eA : (fun x => A (t - I * x)) = fun x => A (t + (-I) * x) := by
    funext x; congr 1; ring
  have eB : (fun x => B (t + I * x)) = fun x => B (t + I * x) := rfl
  have hAc : ContDiffAt ℂ n (fun x => A (t - I * x)) 0 := by
    rw [eA]
    exact (hA.comp (differentiable_const t |>.add (differentiable_id.const_mul _))).contDiff.contDiffAt
  have hBc : ContDiffAt ℂ n (fun x => B (t + I * x)) 0 :=
    (hB.comp (differentiable_const t |>.add (differentiable_id.const_mul _))).contDiff.contDiffAt
  have e : (fun x => A (t - I * x) * B (t + I * x)) =
      (fun x => A (t - I * x)) * fun x => B (t + I * x) := rfl
  rw [e, iteratedDeriv_mul hAc hBc]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eA, hcomp A hA (-I) k, hcomp B hB I (n - k)]

/-- The `n`-th Taylor derivative at `x = 0` of the slice `x ↦ H_λ(t − ix) H_λ(t + ix)`. -/
def heatSliceTaylor (lam t : ℝ) (n : ℕ) : ℂ :=
  iteratedDeriv n (fun x => riemannHeat lam ((t : ℂ) - I * x) * riemannHeat lam ((t : ℂ) + I * x)) 0

/-- The finite-sum form of the slice Taylor derivatives. -/
theorem heatSliceTaylor_eq {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (n : ℕ) :
    heatSliceTaylor lam t n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
      ((-I) ^ k * iteratedDeriv k (riemannHeat lam) t) *
        (I ^ (n - k) * iteratedDeriv (n - k) (riemannHeat lam) t) :=
  iteratedDeriv_slicePair (differentiable_riemannHeat hlam) (differentiable_riemannHeat hlam) t n

/-- `∂_x² S = −H''(t − ix) H(t + ix) + 2 H'(t − ix) H'(t + ix) − H(t − ix) H''(t + ix)`. -/
theorem deriv_deriv_slice {F : ℂ → ℂ} (hF : Differentiable ℂ F) (t : ℂ) :
    deriv (deriv fun x => F (t - I * x) * F (t + I * x)) = fun x =>
      (-1) * (deriv (deriv F) (t - I * x) * F (t + I * x)) +
        2 * (deriv F (t - I * x) * deriv F (t + I * x)) +
          (-1) * (F (t - I * x) * deriv (deriv F) (t + I * x)) := by
  have hF1 : Differentiable ℂ (deriv F) := fun z => ((hF.analyticAt z).deriv).differentiableAt
  have hm : ∀ (G : ℂ → ℂ), Differentiable ℂ G → ∀ x,
      HasDerivAt (fun y => G (t - I * y)) (-I * deriv G (t - I * x)) x := by
    intro G hG x
    have h1 : HasDerivAt (fun y : ℂ => t - I * y) (-I) x := by
      simpa using ((hasDerivAt_id x).const_mul I).const_sub t
    exact ((hG (t - I * x)).hasDerivAt.comp x h1).congr_deriv (by ring)
  have hp : ∀ (G : ℂ → ℂ), Differentiable ℂ G → ∀ x,
      HasDerivAt (fun y => G (t + I * y)) (I * deriv G (t + I * x)) x := by
    intro G hG x
    have h1 : HasDerivAt (fun y : ℂ => t + I * y) I x := by
      simpa using ((hasDerivAt_id x).const_mul I).const_add t
    exact ((hG (t + I * x)).hasDerivAt.comp x h1).congr_deriv (by ring)
  have h1 : deriv (fun x => F (t - I * x) * F (t + I * x)) = fun x =>
      -I * deriv F (t - I * x) * F (t + I * x) + I * (F (t - I * x) * deriv F (t + I * x)) := by
    funext x
    refine ((hm F hF x).mul (hp F hF x)).deriv.trans ?_
    ring
  rw [h1]
  funext x
  have h2 := (((hm (deriv F) hF1 x).const_mul (-I)).mul (hp F hF x)).add
    (((hm F hF x).mul (hp (deriv F) hF1 x)).const_mul I)
  refine (HasDerivAt.deriv (f := fun y => -I * deriv F (t - I * y) * F (t + I * y) +
    I * (F (t - I * y) * deriv F (t + I * y))) h2).trans ?_
  ring_nf
  rw [I_sq]
  ring

/-- `D_{n+2}` in terms of the derivatives of `H_λ` at `t`. -/
theorem heatSliceTaylor_add_two {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (n : ℕ) :
    heatSliceTaylor lam t (n + 2) = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
      ((-I) ^ k * I ^ (n - k)) *
        (-(iteratedDeriv (k + 2) (riemannHeat lam) t * iteratedDeriv (n - k) (riemannHeat lam) t) +
          2 * (iteratedDeriv (k + 1) (riemannHeat lam) t *
            iteratedDeriv (n - k + 1) (riemannHeat lam) t) -
          iteratedDeriv k (riemannHeat lam) t * iteratedDeriv (n - k + 2) (riemannHeat lam) t) := by
  set F := riemannHeat lam with hFdef
  have hF : Differentiable ℂ F := differentiable_riemannHeat hlam
  have hF1 : Differentiable ℂ (deriv F) := fun z => ((hF.analyticAt z).deriv).differentiableAt
  have hF2 : Differentiable ℂ (deriv (deriv F)) :=
    fun z => ((hF1.analyticAt z).deriv).differentiableAt
  have hit : ∀ k, iteratedDeriv k (deriv (deriv F)) = iteratedDeriv (k + 2) F := by
    intro k; rw [iteratedDeriv_succ', iteratedDeriv_succ']
  have hit1 : ∀ k, iteratedDeriv k (deriv F) = iteratedDeriv (k + 1) F := by
    intro k; rw [iteratedDeriv_succ']
  have hd : ∀ (A B : ℂ → ℂ), Differentiable ℂ A → Differentiable ℂ B →
      Differentiable ℂ (fun x => A ((t : ℂ) - I * x) * B ((t : ℂ) + I * x)) := by
    intro A B hA hB
    exact (hA.comp (differentiable_const _ |>.sub (differentiable_id.const_mul _))).mul
      (hB.comp (differentiable_const _ |>.add (differentiable_id.const_mul _)))
  set g₁ : ℂ → ℂ := fun x => deriv (deriv F) ((t : ℂ) - I * x) * F ((t : ℂ) + I * x) with hg₁
  set g₂ : ℂ → ℂ := fun x => deriv F ((t : ℂ) - I * x) * deriv F ((t : ℂ) + I * x) with hg₂
  set g₃ : ℂ → ℂ := fun x => F ((t : ℂ) - I * x) * deriv (deriv F) ((t : ℂ) + I * x) with hg₃
  have hd₁ : Differentiable ℂ g₁ := hd _ _ hF2 hF
  have hd₂ : Differentiable ℂ g₂ := hd _ _ hF1 hF1
  have hd₃ : Differentiable ℂ g₃ := hd _ _ hF hF2
  unfold heatSliceTaylor
  rw [iteratedDeriv_succ', iteratedDeriv_succ', deriv_deriv_slice hF]
  have e : (fun x => (-1) * (deriv (deriv F) ((t : ℂ) - I * x) * F ((t : ℂ) + I * x)) +
        2 * (deriv F ((t : ℂ) - I * x) * deriv F ((t : ℂ) + I * x)) +
          (-1) * (F ((t : ℂ) - I * x) * deriv (deriv F) ((t : ℂ) + I * x))) =
      ((fun x => (-1) * g₁ x) + fun x => 2 * g₂ x) + fun x => (-1) * g₃ x := rfl
  have c₁ : ContDiffAt ℂ n (fun x => (-1) * g₁ x) 0 := (hd₁.const_mul _).contDiff.contDiffAt
  have c₂ : ContDiffAt ℂ n (fun x => 2 * g₂ x) 0 := (hd₂.const_mul _).contDiff.contDiffAt
  have c₃ : ContDiffAt ℂ n (fun x => (-1) * g₃ x) 0 := (hd₃.const_mul _).contDiff.contDiffAt
  have c₁₂ : ContDiffAt ℂ n ((fun x => (-1) * g₁ x) + fun x => 2 * g₂ x) 0 := c₁.add c₂
  rw [e, iteratedDeriv_add c₁₂ c₃, iteratedDeriv_add c₁ c₂,
    iteratedDeriv_const_mul _ hd₁.contDiff.contDiffAt,
    iteratedDeriv_const_mul _ hd₂.contDiff.contDiffAt,
    iteratedDeriv_const_mul _ hd₃.contDiff.contDiffAt]
  simp only [hg₁, hg₂, hg₃]
  rw [iteratedDeriv_slicePair hF2 hF, iteratedDeriv_slicePair hF1 hF1,
    iteratedDeriv_slicePair hF hF2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hit, hit, hit1, hit1]
  ring

/-- `t`-derivative of a product of two derivatives of `H_λ` along the real axis. -/
theorem hasDerivAt_heatProduct_height {lam : ℝ} (hlam : 0 ≤ lam) (a b : ℕ) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => iteratedDeriv a (riemannHeat lam) (τ : ℂ) *
        iteratedDeriv b (riemannHeat lam) (τ : ℂ))
      (iteratedDeriv (a + 1) (riemannHeat lam) t * iteratedDeriv b (riemannHeat lam) t +
        iteratedDeriv a (riemannHeat lam) t * iteratedDeriv (b + 1) (riemannHeat lam) t) t :=
  (hasDerivAt_iteratedDeriv_riemannHeat hlam a t).comp_ofReal.mul
    (hasDerivAt_iteratedDeriv_riemannHeat hlam b t).comp_ofReal

/-- **The second height derivative of `D_n`.** -/
theorem deriv_deriv_heatSliceTaylor_height {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (t : ℝ) :
    deriv (deriv fun τ : ℝ => heatSliceTaylor lam τ n) t =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        (iteratedDeriv (k + 2) (riemannHeat lam) t * iteratedDeriv (n - k) (riemannHeat lam) t +
          2 * (iteratedDeriv (k + 1) (riemannHeat lam) t *
            iteratedDeriv (n - k + 1) (riemannHeat lam) t) +
          iteratedDeriv k (riemannHeat lam) t * iteratedDeriv (n - k + 2) (riemannHeat lam) t) := by
  set H : ℕ → ℝ → ℂ := fun k τ => iteratedDeriv k (riemannHeat lam) (τ : ℂ) with hH
  have hD : (fun τ : ℝ => heatSliceTaylor lam τ n) = fun τ =>
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        (H k τ * H (n - k) τ) := by
    funext τ
    rw [heatSliceTaylor_eq hlam]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hH]
    ring
  have hD1 : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ =>
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        (H k τ * H (n - k) τ))
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        (H (k + 1) τ * H (n - k) τ + H k τ * H (n - k + 1) τ)) τ := by
    intro τ
    exact HasDerivAt.fun_sum fun k _ =>
      (hasDerivAt_heatProduct_height hlam k (n - k) τ).const_mul _
  have hD2 : HasDerivAt (fun τ : ℝ =>
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        (H (k + 1) τ * H (n - k) τ + H k τ * H (n - k + 1) τ))
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        ((H (k + 2) t * H (n - k) t + H (k + 1) t * H (n - k + 1) t) +
          (H (k + 1) t * H (n - k + 1) t + H k t * H (n - k + 2) t))) t :=
    HasDerivAt.fun_sum fun k _ =>
      ((hasDerivAt_heatProduct_height hlam (k + 1) (n - k) t).add
        (hasDerivAt_heatProduct_height hlam k (n - k + 1) t)).const_mul _
  rw [hD]
  have e1 : deriv (fun τ : ℝ =>
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        (H k τ * H (n - k) τ)) = fun τ =>
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        (H (k + 1) τ * H (n - k) τ + H k τ * H (n - k + 1) τ) := by
    funext τ; exact (hD1 τ).deriv
  rw [e1, hD2.deriv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hH]
  ring

/-- **The slice hierarchy along the flow.**  For `λ > 0`,
`∂_λ D_n(λ, t) = ½ (D_{n+2}(λ, t) − ∂_t² D_n(λ, t))`. -/
theorem hasDerivAt_heatSliceTaylor_time {lam : ℝ} (hlam : 0 < lam) (t : ℝ) (n : ℕ) :
    HasDerivAt (fun s => heatSliceTaylor s t n)
      ((heatSliceTaylor lam t (n + 2) - deriv (deriv fun τ : ℝ => heatSliceTaylor lam τ n) t) / 2)
      lam := by
  set H : ℕ → ℝ → ℂ := fun k s => iteratedDeriv k (riemannHeat s) (t : ℂ) with hH
  have hev : (fun s => heatSliceTaylor s t n) =ᶠ[𝓝 lam] fun s =>
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        (H k s * H (n - k) s) := by
    filter_upwards [lt_mem_nhds hlam] with s hs
    rw [heatSliceTaylor_eq hs.le]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hH]
    ring
  have hT : HasDerivAt (fun s =>
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        (H k s * H (n - k) s))
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((-I) ^ k * I ^ (n - k)) *
        (-H (k + 2) lam * H (n - k) lam + H k lam * -H (n - k + 2) lam)) lam :=
    HasDerivAt.fun_sum fun k _ =>
      ((hasDerivAt_iteratedDeriv_riemannHeat_time hlam k t).mul
        (hasDerivAt_iteratedDeriv_riemannHeat_time hlam (n - k) t)).const_mul _
  refine (hT.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [heatSliceTaylor_add_two hlam.le, deriv_deriv_heatSliceTaylor_height hlam.le,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hH]
  ring

/-- **The hierarchy in coefficient form.**  With `c_n = D_n/n!`,
`∂_λ c_n = ½ (n+2)(n+1) c_{n+2} − ½ ∂_t² c_n`. -/
theorem hasDerivAt_heatSliceCoeff_time {lam : ℝ} (hlam : 0 < lam) (t : ℝ) (n : ℕ) :
    HasDerivAt (fun s => (n.factorial : ℂ)⁻¹ * heatSliceTaylor s t n)
      ((((n + 2) * (n + 1) : ℕ) : ℂ) / 2 *
          (((n + 2).factorial : ℂ)⁻¹ * heatSliceTaylor lam t (n + 2)) -
        (n.factorial : ℂ)⁻¹ * deriv (deriv fun τ : ℝ => heatSliceTaylor lam τ n) t / 2) lam := by
  refine ((hasDerivAt_heatSliceTaylor_time hlam t n).const_mul _).congr_deriv ?_
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hfac : ((n + 2).factorial : ℂ) = (((n + 2) * (n + 1) : ℕ) : ℂ) * n.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hf2 : (((n + 2) * (n + 1) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
  rw [hfac]
  field_simp

end

end RHTower.DeBruijn
