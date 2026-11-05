import GaloisForLFunctions.FiniteFreeProbability.BackwardHeatJensenNonRealRootCount
import GaloisForLFunctions.FiniteFreeProbability.EulerFactorStability
import GaloisForLFunctions.RHTower.XiCosineShiftHeatStrip

/-!
# Bernoulli components cannot repair the Gaussian deficit

The Bernoulli (cosine) shift `p ↦ p(X + ib) + p(X − ib)` is, on polynomials of degree `≤ d`, the
finite free convolution with the real-rooted two-point polynomial `(X+ib)^d + (X−ib)^d`. By the
Hermite–Biehler theorem it preserves real-rootedness (`p(X + ib)` has its roots in `Im = −b`).

**Theorem.** For all `a, t > 0`, the Bernoulli shift by `a/d` of the backward heat flow
`e^{(t/d²)D²} J_d` of the Jensen polynomial of `Ξ` is not real-rooted for all large `d`.

Since Bernoulli shifts preserve real-rootedness, this strengthens the finite free
de Bruijn–Newman law: a Gaussian deficit at scale `t/d²` cannot be compensated by any two-point
factor at scale `a/d`, however large `a`. The limit object is the cosine shift
`H_{−t}(z + ia) + H_{−t}(z − ia)`, whose non-real zeros are supplied by the cosine-shift
de Bruijn–Newman theorem.
-/

open Polynomial Filter Topology Complex Metric MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

/-- The Bernoulli shift `p(X + ib) + p(X − ib)` of a real polynomial, over `ℂ`. -/
def cosAvg (b : ℝ) (p : ℝ[X]) : ℂ[X] :=
  (p.map (algebraMap ℝ ℂ)).comp (X + C (I * b)) + (p.map (algebraMap ℝ ℂ)).comp (X + C (-(I * b)))

theorem eval_cosAvg (b : ℝ) (p : ℝ[X]) (w : ℂ) :
    (cosAvg b p).eval w = (p.map (algebraMap ℝ ℂ)).eval (w + I * b) +
      (p.map (algebraMap ℝ ℂ)).eval (w - I * b) := by
  simp [cosAvg, eval_comp, sub_eq_add_neg]

theorem conjPoly_map_comp (p : ℝ[X]) (c : ℂ) :
    conjPoly ((p.map (algebraMap ℝ ℂ)).comp (X + C c)) =
      (p.map (algebraMap ℝ ℂ)).comp (X + C (conj c)) := by
  rw [conjPoly, Polynomial.map_comp, Polynomial.map_map]
  congr 1
  · congr 1; ext r; simp
  · simp

theorem conjPoly_cosAvg (b : ℝ) (p : ℝ[X]) : conjPoly (cosAvg b p) = cosAvg b p := by
  rw [cosAvg, conjPoly, Polynomial.map_add, ← conjPoly, ← conjPoly, conjPoly_map_comp,
    conjPoly_map_comp, add_comm]
  congr 3 <;> simp [Complex.conj_ofReal]

theorem im_coeff_cosAvg (b : ℝ) (p : ℝ[X]) (k : ℕ) : ((cosAvg b p).coeff k).im = 0 := by
  have h := congrArg (fun P => P.coeff k) (conjPoly_cosAvg b p)
  simp only [conjPoly, coeff_map] at h
  exact Complex.conj_eq_iff_im.1 h

/-- The real polynomial carrying the (real) coefficients of `cosAvg b p`. -/
def realCosAvg (b : ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range ((cosAvg b p).natDegree + 1), C (((cosAvg b p).coeff k).re) * X ^ k

theorem map_realCosAvg (b : ℝ) (p : ℝ[X]) :
    (realCosAvg b p).map (algebraMap ℝ ℂ) = cosAvg b p := by
  ext k
  rw [coeff_map, realCosAvg, finsetSum_coeff]
  by_cases hk : k ≤ (cosAvg b p).natDegree
  · rw [Finset.sum_eq_single k]
    · simp only [coeff_C_mul_X_pow, if_true]
      exact Complex.ext (by simp) (by simp [im_coeff_cosAvg])
    · intro j _ hj; rw [coeff_C_mul_X_pow, if_neg (Ne.symm hj)]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [Finset.sum_eq_zero fun j hj => by
      rw [coeff_C_mul_X_pow, if_neg (by have := Finset.mem_range.1 hj; omega)],
      coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- **Bernoulli shifts preserve real-rootedness** (Hermite–Biehler). -/
theorem splits_realCosAvg_of_splits {b : ℝ} (hb : 0 < b) {p : ℝ[X]} (hp : p.Splits) (hp0 : p ≠ 0)
    (hdeg : 1 ≤ p.natDegree) : (realCosAvg b p).Splits := by
  set φ := algebraMap ℝ ℂ
  set Q := (p.map φ).comp (X + C (I * b))
  have hlin : (X + C (I * b) : ℂ[X]).natDegree = 1 := natDegree_X_add_C _
  have hQdeg : Q.natDegree = p.natDegree := by
    rw [natDegree_comp, hlin, mul_one, natDegree_map_eq_of_injective φ.injective]
  have hQ0 : Q ≠ 0 := fun h0 => by
    rw [h0, natDegree_zero] at hQdeg; omega
  have hQroots : ∀ r, Q.IsRoot r → r.im < 0 := by
    intro r hr
    have hroot : (aeval (r + I * b) p : ℂ) = 0 := by
      have := hr; simp only [IsRoot, Q, eval_comp, eval_add, eval_X, eval_C] at this
      rwa [aeval_def, eval₂_eq_eval_map]
    have := GaloisForLFunctions.HTGeometry.im_eq_zero_of_splits hp hp0 hroot
    simp at this
    linarith
  have hsum : cosAvg b p = Q + conjPoly Q := by
    have hc : conj (I * (b : ℂ)) = -(I * b) := by simp
    rw [cosAvg, conjPoly_map_comp, hc]
  refine GaloisForLFunctions.HTGeometry.splits_of_forall_complex_root_real
    (realCosAvg b p).natDegree _ le_rfl fun r hr => ?_
  have hr' : (Q + conjPoly Q).IsRoot r := by
    rw [← hsum, ← map_realCosAvg, IsRoot, ← eval₂_eq_eval_map, ← aeval_def]; exact hr
  exact im_eq_zero_of_isRoot_add_conjPoly hQ0 (by omega) hQroots hr'

/-- `H_{−t}(ia) + H_{−t}(−ia) ≠ 0`: both values are integrals of positive functions. -/
theorem riemannHeat_neg_cosine_zero_ne {τ : ℝ} (hτ : 0 ≤ τ) (a : ℝ) :
    riemannHeat (-τ) (0 + a * I) + riemannHeat (-τ) (0 - a * I) ≠ 0 := by
  set k : ℝ → ℝ := fun x => riemannKernelReal x * Real.exp (-τ * x ^ 2)
  have hk := superExpKernel_mul_exp_neg_sq hτ
  have hval : ∀ c : ℝ, riemannHeat (-τ) (c * I) = ((∫ x, k x * Real.exp (-(c * x))) : ℝ) := by
    intro c
    rw [riemannHeat, cosTransform, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [k]
    have : I * (c * I) * x = (-(c * x) : ℝ) := by push_cast; ring_nf; rw [I_sq]; ring
    rw [this, ← Complex.ofReal_exp]; push_cast; ring
  have hpos : ∀ c : ℝ, 0 < ∫ x, k x * Real.exp (-(c * x)) := by
    intro c
    have hint : Integrable (fun x => k x * Real.exp (-(c * x))) := by
      refine (hk.integrable_mul_exp |c|).mono'
        ((hk.continuous.mul (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk.nonneg x) (Real.exp_pos _).le)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hk.nonneg x)
      rw [← abs_mul]; exact neg_le_abs _
    rw [integral_pos_iff_support_of_nonneg (fun x => mul_nonneg (hk.nonneg x)
      (Real.exp_pos _).le) hint]
    have hsupp : Function.support (fun x => k x * Real.exp (-(c * x))) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (mul_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)) (Real.exp_pos _)).ne'
    rw [hsupp]; simp
  rw [zero_add, zero_sub, show -(a * I) = ((-a : ℝ) : ℂ) * I by push_cast; ring, hval, hval,
    ← Complex.ofReal_add]
  exact Complex.ofReal_ne_zero.2 (by linarith [hpos a, hpos (-a)])

/-- **Bernoulli robustness of the finite free de Bruijn–Newman law.** -/
theorem eventually_not_splits_realCosAvg_heatOp_jensenPoly_XiC {a τ : ℝ} (ha : 0 < a)
    (hτ : 0 < τ) :
    ∀ᶠ d : ℕ in atTop, ¬ (realCosAvg (a / d) (heatOp (τ / (d : ℝ) ^ 2) d
      (jensenPoly (realTaylorCoeff XiC) d))).Splits := by
  by_contra h
  rw [Filter.not_eventually] at h
  simp only [not_not] at h
  obtain ⟨φ, hφ, hsplit⟩ := Filter.extraction_of_frequently_atTop h
  set ψ : ℕ → ℕ := fun m => φ (m + 1)
  have hψpos : ∀ m, 0 < ψ m := fun m => lt_of_le_of_lt (Nat.zero_le _) (hφ (Nat.lt_succ_self m))
  have hψ : StrictMono ψ := fun i j hij => hφ (by omega)
  set P : ℕ → ℝ[X] := fun d => heatOp (τ / (d : ℝ) ^ 2) d (jensenPoly (realTaylorCoeff XiC) d)
  set p : ℕ → ℝ[X] := fun m => (realCosAvg (a / ψ m) (P (ψ m))).comp (C ((ψ m : ℝ)⁻¹) * X)
  have hpsplit : ∀ m, (p m).Splits := fun m =>
    (splits_iff_comp_splits_of_natDegree_eq_one (by
      rw [natDegree_C_mul_X _ (inv_ne_zero (by exact_mod_cast (hψpos m).ne'))])).1 (hsplit (m + 1))
  set G : ℂ → ℂ := fun z => riemannHeat (-τ) (z + a * I) + riemannHeat (-τ) (z - a * I)
  have hpeval : ∀ m, polyEvalC (p m) = fun z =>
      scaledHeatJensen τ (ψ m) (z + a * I) + scaledHeatJensen τ (ψ m) (z - a * I) := fun m => by
    funext z
    have hd : ((ψ m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (hψpos m).ne'
    rw [polyEvalC_eq_eval_map, Polynomial.map_comp, eval_comp, map_realCosAvg, eval_cosAvg]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_mul, eval_C, eval_X,
      scaledHeatJensen, P]
    congr 2 <;> · push_cast; field_simp
  have hF := tendstoLocallyUniformly_comp_strictMono
    (tendstoLocallyUniformly_scaledHeatJensen hτ.le) hψ
  have h1 := hF.comp (fun z => z + a * I) (continuous_id.add continuous_const)
  have h2 := hF.comp (fun z => z - a * I) (continuous_id.sub continuous_const)
  have hconv : TendstoLocallyUniformly (fun m => polyEvalC (p m)) G atTop := by
    simp_rw [hpeval]
    exact h1.add h2
  have hLP : LaguerrePolya G := ⟨p, hpsplit, hconv⟩
  obtain ⟨z, hz, him⟩ := (cosineShift_deBruijnNewman_bounds ha).1 τ hτ
  exact him.ne (im_eq_zero_of_laguerrePolya hLP (riemannHeat_neg_cosine_zero_ne hτ.le a) hz)

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_not_splits_realCosAvg_heatOp_jensenPoly_XiC
#print axioms FiniteFreeProbability.splits_realCosAvg_of_splits
