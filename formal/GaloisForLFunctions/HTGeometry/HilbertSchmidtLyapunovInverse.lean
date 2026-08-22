import GaloisForLFunctions.HTGeometry.HilbertSchmidtSandwichBounds
import GaloisForLFunctions.HTGeometry.OperatorLyapunovEquation
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The Lyapunov inverse preserves the Hilbert–Schmidt class

If `v` is strictly positive and `v y + y v = q` with `q` Hilbert–Schmidt, then `y` itself is
Hilbert–Schmidt.  The proof replaces the semigroup integral `y = ∫₀^∞ e^{-tv} q e^{-tv} dt` by the
Picard iteration for the same fixed point: writing `w = v - μ` for the midpoint `μ` of a Loewner
interval containing `v`, the equation reads `y = (2μ)⁻¹ (q - w y - y w)`, and the right-hand side
is a contraction both in the operator norm and in the Hilbert–Schmidt norm.  Starting from `0`,
every iterate is Hilbert–Schmidt with a uniform Hilbert–Schmidt bound, and the iterates converge to
`y` in operator norm; a Fatou argument on finite partial sums of `∑ᵢ ‖y eᵢ‖²` then transfers the
bound to `y`.
-/

open scoped BigOperators InnerProductSpace Ring
open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

omit [CompleteSpace F] in
/-- `hsNorm` squares back to `hsNormSq`. -/
theorem sq_hsNorm (T : E →L[𝕜] F) : (hsNorm T) ^ 2 = hsNormSq T :=
  Real.sq_sqrt (hsNormSq_nonneg T)

omit [CompleteSpace F] [CompleteSpace G] in
/-- Operator-norm bound for a left composition, in `hsNorm` form. -/
theorem hsNorm_comp_left_le {S : F →L[𝕜] G} {Y : E →L[𝕜] F} (hY : IsHilbertSchmidt Y) :
    hsNorm (S ∘L Y) ≤ ‖S‖ * hsNorm Y := by
  have h : hsNormSq (S ∘L Y) ≤ ‖S‖ ^ 2 * hsNormSq Y :=
    hsNormSq_comp_left_le hY fun v => by
      calc ‖S v‖ ^ 2 ≤ (‖S‖ * ‖v‖) ^ 2 := by gcongr; exact S.le_opNorm v
        _ = ‖S‖ ^ 2 * ‖v‖ ^ 2 := by ring
  have h2 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg S)] at h2

/-- Operator-norm bound for a right composition, in `hsNorm` form. -/
theorem hsNorm_comp_right_le {Y : F →L[𝕜] G} {T : E →L[𝕜] F} (hY : IsHilbertSchmidt Y) :
    hsNorm (Y ∘L T) ≤ hsNorm Y * ‖T‖ := by
  have h : hsNormSq (Y ∘L T) ≤ ‖T‖ ^ 2 * hsNormSq Y :=
    hsNormSq_comp_right_le hY fun v => by
      calc ‖adjoint T v‖ ^ 2 ≤ (‖adjoint T‖ * ‖v‖) ^ 2 := by
            gcongr; exact (adjoint T).le_opNorm v
        _ = ‖T‖ ^ 2 * ‖v‖ ^ 2 := by rw [adjoint.norm_map]; ring
  have h2 := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg T)] at h2
  calc hsNorm (Y ∘L T) ≤ ‖T‖ * hsNorm Y := h2
    _ = hsNorm Y * ‖T‖ := mul_comm _ _

omit [CompleteSpace F] in
/-- The zero operator has vanishing Hilbert–Schmidt norm. -/
theorem hsNormSq_zero : hsNormSq (0 : E →L[𝕜] F) = 0 := by
  show ∑' i, ‖(0 : E →L[𝕜] F) (hsBasis 𝕜 E i)‖ ^ 2 = 0
  simp

omit [CompleteSpace F] in
/-- The zero operator has vanishing Hilbert–Schmidt norm. -/
theorem hsNorm_zero : hsNorm (0 : E →L[𝕜] F) = 0 := by
  show Real.sqrt (hsNormSq (0 : E →L[𝕜] F)) = 0
  rw [hsNormSq_zero, Real.sqrt_zero]

omit [CompleteSpace F] in
/-- `hsNorm` obeys the triangle inequality for differences. -/
theorem hsNorm_sub_le {S T : E →L[𝕜] F} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    hsNorm (S - T) ≤ hsNorm S + hsNorm T := by
  have hneg : hsNorm (-T) = hsNorm T := by
    show Real.sqrt (hsNormSq (-T)) = Real.sqrt (hsNormSq T)
    rw [hsNormSq_neg_eq_self]
  rw [sub_eq_add_neg, ← hneg]
  exact hsNorm_add_le hS hT.neg

omit [CompleteSpace F] in
/-- A finite sum of Hilbert–Schmidt operators is Hilbert–Schmidt. -/
theorem IsHilbertSchmidt.sum {ι : Type*} (s : Finset ι) {S : ι → E →L[𝕜] F}
    (hS : ∀ i ∈ s, IsHilbertSchmidt (S i)) : IsHilbertSchmidt (∑ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHilbertSchmidt_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hS i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hS j (Finset.mem_insert_of_mem hj))

/-- The Hilbert–Schmidt inner product is additive over finite sums in its first slot. -/
theorem hsInner_sum_left {ι : Type*} (s : Finset ι) {S : ι → E →L[𝕜] F} {T : E →L[𝕜] F}
    (hS : ∀ i ∈ s, IsHilbertSchmidt (S i)) (hT : IsHilbertSchmidt T) :
    hsInner (∑ i ∈ s, S i) T = ∑ i ∈ s, hsInner (S i) T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hsInner]
  | insert i s hi ih =>
    have hmem : ∀ j ∈ s, IsHilbertSchmidt (S j) := fun j hj =>
      hS j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hsInner_add_left (hS i (Finset.mem_insert_self i s))
        (IsHilbertSchmidt.sum s hmem) hT, ih hmem]

omit [CompleteSpace F] in
/-- **Fatou for the Hilbert–Schmidt class.**  A pointwise limit of Hilbert–Schmidt operators with
a uniform Hilbert–Schmidt bound is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_of_tendsto {yn : ℕ → E →L[𝕜] F} {y : E →L[𝕜] F} {C : ℝ}
    (hHS : ∀ n, IsHilbertSchmidt (yn n)) (hbd : ∀ n, hsNormSq (yn n) ≤ C)
    (hlim : ∀ e : E, Tendsto (fun n => yn n e) atTop (nhds (y e))) :
    IsHilbertSchmidt y := by
  refine summable_of_sum_le (c := C) (fun i => by positivity) fun s => ?_
  have hts : Tendsto (fun n => ∑ i ∈ s, ‖yn n (hsBasis 𝕜 E i)‖ ^ 2) atTop
      (nhds (∑ i ∈ s, ‖y (hsBasis 𝕜 E i)‖ ^ 2)) :=
    tendsto_finsetSum _ fun i _ => ((hlim _).norm).pow 2
  refine le_of_tendsto hts (Eventually.of_forall fun n => ?_)
  exact ((hHS n).sum_le_tsum s (fun i _ => by positivity)).trans (hbd n)

omit [CompleteSpace F] in
/-- **Fatou bound for the Hilbert–Schmidt norm.** -/
theorem hsNormSq_le_of_tendsto {yn : ℕ → E →L[𝕜] F} {y : E →L[𝕜] F} {C : ℝ}
    (hHS : ∀ n, IsHilbertSchmidt (yn n)) (hbd : ∀ n, hsNormSq (yn n) ≤ C)
    (hlim : ∀ e : E, Tendsto (fun n => yn n e) atTop (nhds (y e))) :
    hsNormSq y ≤ C := by
  have hy : IsHilbertSchmidt y := isHilbertSchmidt_of_tendsto hHS hbd hlim
  refine Summable.tsum_le_of_sum_le hy fun s => ?_
  have hts : Tendsto (fun n => ∑ i ∈ s, ‖yn n (hsBasis 𝕜 E i)‖ ^ 2) atTop
      (nhds (∑ i ∈ s, ‖y (hsBasis 𝕜 E i)‖ ^ 2)) :=
    tendsto_finsetSum _ fun i _ => ((hlim _).norm).pow 2
  refine le_of_tendsto hts (Eventually.of_forall fun n => ?_)
  exact ((hHS n).sum_le_tsum s (fun i _ => by positivity)).trans (hbd n)

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
private lemma norm_real_smul_apply (r : ℝ) (T : E →L[ℂ] F) :
    (fun i => ‖(r • T) (hsBasis ℂ E i)‖ ^ 2)
      = fun i => r ^ 2 * ‖T (hsBasis ℂ E i)‖ ^ 2 := by
  funext i
  rw [smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

omit [CompleteSpace F] in
/-- The Hilbert–Schmidt class is stable under real scalar multiplication. -/
theorem IsHilbertSchmidt.real_smul {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T) (r : ℝ) :
    IsHilbertSchmidt (r • T) := by
  have h : Summable (fun i => r ^ 2 * ‖T (hsBasis ℂ E i)‖ ^ 2) := hT.mul_left (r ^ 2)
  show Summable (fun i => ‖(r • T) (hsBasis ℂ E i)‖ ^ 2)
  rw [norm_real_smul_apply r T]
  exact h

omit [CompleteSpace F] in
/-- `hsNorm` is absolutely homogeneous for real scalars. -/
theorem hsNorm_real_smul (r : ℝ) (T : E →L[ℂ] F) : hsNorm (r • T) = |r| * hsNorm T := by
  have hsq : hsNormSq (r • T) = r ^ 2 * hsNormSq T := by
    show ∑' i, ‖(r • T) (hsBasis ℂ E i)‖ ^ 2 = r ^ 2 * ∑' i, ‖T (hsBasis ℂ E i)‖ ^ 2
    rw [norm_real_smul_apply r T, tsum_mul_left]
  show Real.sqrt (hsNormSq (r • T)) = |r| * Real.sqrt (hsNormSq T)
  rw [hsq, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

omit [CompleteSpace F] in
/-- Real homogeneity of the Hilbert–Schmidt inner product in its first slot. -/
theorem hsInner_real_smul_left (r : ℝ) (S T : E →L[ℂ] F) :
    hsInner (r • S) T = (r : ℂ) * hsInner S T := by
  show ∑' i, inner ℂ ((r • S) (hsBasis ℂ E i)) (T (hsBasis ℂ E i))
      = (r : ℂ) * ∑' i, inner ℂ (S (hsBasis ℂ E i)) (T (hsBasis ℂ E i))
  rw [← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [smul_apply, ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal]

omit [CompleteSpace F] in
/-- Real homogeneity of the Hilbert–Schmidt inner product in its second slot. -/
theorem hsInner_real_smul_right (r : ℝ) (S T : E →L[ℂ] F) :
    hsInner S (r • T) = (r : ℂ) * hsInner S T := by
  show ∑' i, inner ℂ (S (hsBasis ℂ E i)) ((r • T) (hsBasis ℂ E i))
      = (r : ℂ) * ∑' i, inner ℂ (S (hsBasis ℂ E i)) (T (hsBasis ℂ E i))
  rw [← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [smul_apply, ← Complex.coe_smul, inner_smul_right]

end ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)]

/-- **The Lyapunov inverse preserves the Hilbert–Schmidt class.**  If `v` is strictly positive and
`v y + y v` is Hilbert–Schmidt, then so is `y`. -/
theorem isHilbertSchmidt_of_lyapunov [StarOrderedRing (E →L[ℂ] E)]
    {v y q : E →L[ℂ] E} (hv : IsStrictlyPositive v)
    (hq : IsHilbertSchmidt q) (heq : v * y + y * v = q) : IsHilbertSchmidt y := by
  rcases subsingleton_or_nontrivial (E →L[ℂ] E) with hsub | hnt
  · exact (Subsingleton.elim y 0) ▸ isHilbertSchmidt_zero
  obtain ⟨μ₁, hμ₁pos, hμ₁le⟩ := exists_pos_smul_one_le hv
  have hvM : v ≤ ‖v‖ • (1 : E →L[ℂ] E) := by
    have h := hv.isSelfAdjoint.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hμM : μ₁ ≤ ‖v‖ := by
    have h0 : (0 : E →L[ℂ] E) ≤ μ₁ • (1 : E →L[ℂ] E) :=
      smul_nonneg hμ₁pos.le zero_le_one
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hμ₁le
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hμ₁pos, norm_one, mul_one] at h
  obtain ⟨μ, ρ, hμpos, hρnn, hρμ, hwn0⟩ :
      ∃ μ ρ : ℝ, 0 < μ ∧ 0 ≤ ρ ∧ ρ < μ ∧ ‖v - μ • (1 : E →L[ℂ] E)‖ ≤ ρ :=
    ⟨(μ₁ + ‖v‖) / 2, (‖v‖ - μ₁) / 2, by linarith, by linarith, by linarith,
      norm_sub_midpoint_le hμM hv.isSelfAdjoint hμ₁le hvM⟩
  obtain ⟨w, hwdef, hwn⟩ : ∃ w : E →L[ℂ] E, w = v - μ • (1 : E →L[ℂ] E) ∧ ‖w‖ ≤ ρ :=
    ⟨_, rfl, hwn0⟩
  have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have h2μ : (0 : ℝ) < 2 * μ := by linarith
  have h2μinv : (0 : ℝ) < (2 * μ)⁻¹ := inv_pos.mpr h2μ
  have hfix : y = (2 * μ)⁻¹ • (q - w * y - y * w) := by
    have hrw : q - w * y - y * w = (2 * μ) • y := by
      rw [← heq, hwdef, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    rw [hrw, smul_smul, inv_mul_cancel₀ (ne_of_gt h2μ), one_smul]
  obtain ⟨yn, hy0, hstep⟩ : ∃ yn : ℕ → (E →L[ℂ] E), yn 0 = 0 ∧
      ∀ n, yn (n + 1) = (2 * μ)⁻¹ • (q - w * yn n - yn n * w) :=
    ⟨fun n => (fun z => (2 * μ)⁻¹ • (q - w * z - z * w))^[n] 0, rfl,
      fun n => Function.iterate_succ_apply' _ n 0⟩
  have hHS : ∀ n, IsHilbertSchmidt (yn n) := by
    intro n
    induction n with
    | zero => rw [hy0]; exact isHilbertSchmidt_zero
    | succ n ih =>
      rw [hstep]
      exact IsHilbertSchmidt.real_smul
        ((hq.sub (ih.comp_left w)).sub (ih.comp_right w)) _
  obtain ⟨K, hKnn, hqK⟩ : ∃ K : ℝ, 0 ≤ K ∧ hsNorm q = 2 * (μ - ρ) * K := by
    have hne : (0 : ℝ) < 2 * (μ - ρ) := by linarith
    refine ⟨hsNorm q / (2 * (μ - ρ)), div_nonneg (hsNorm_nonneg q) hne.le, ?_⟩
    field_simp
    rw [mul_div_assoc, div_self (by linarith : (μ : ℝ) - ρ ≠ 0), mul_one]
  have hbound : ∀ n, hsNorm (yn n) ≤ K := by
    intro n
    induction n with
    | zero => rw [hy0, hsNorm_zero]; exact hKnn
    | succ n ih =>
      have hHSn := hHS n
      have hsub1 : IsHilbertSchmidt (q - w * yn n : E →L[ℂ] E) := hq.sub (hHSn.comp_left w)
      have h1 : hsNorm (w * yn n : E →L[ℂ] E) ≤ ‖w‖ * hsNorm (yn n) :=
        hsNorm_comp_left_le hHSn
      have h2 : hsNorm (yn n * w : E →L[ℂ] E) ≤ hsNorm (yn n) * ‖w‖ :=
        hsNorm_comp_right_le hHSn
      have h3 : hsNorm (q - w * yn n - yn n * w : E →L[ℂ] E)
          ≤ hsNorm q + ‖w‖ * hsNorm (yn n) + hsNorm (yn n) * ‖w‖ := by
        have ha : hsNorm ((q - w * yn n) - yn n * w : E →L[ℂ] E)
            ≤ hsNorm (q - w * yn n : E →L[ℂ] E) + hsNorm (yn n * w : E →L[ℂ] E) :=
          hsNorm_sub_le hsub1 (hHSn.comp_right w)
        have hb : hsNorm (q - w * yn n : E →L[ℂ] E)
            ≤ hsNorm q + hsNorm (w * yn n : E →L[ℂ] E) :=
          hsNorm_sub_le hq (hHSn.comp_left w)
        linarith
      have hnn : 0 ≤ hsNorm (yn n) := hsNorm_nonneg _
      have hstep2 : hsNorm q + ‖w‖ * hsNorm (yn n) + hsNorm (yn n) * ‖w‖
          ≤ 2 * (μ - ρ) * K + 2 * ρ * K := by
        have hc : ‖w‖ * hsNorm (yn n) ≤ ρ * K := mul_le_mul hwn ih hnn hρnn
        have hd : hsNorm (yn n) * ‖w‖ ≤ K * ρ := mul_le_mul ih hwn hwnn hKnn
        rw [hqK]; nlinarith
      rw [hstep, hsNorm_real_smul, abs_of_pos h2μinv]
      calc (2 * μ)⁻¹ * hsNorm (q - w * yn n - yn n * w : E →L[ℂ] E)
          ≤ (2 * μ)⁻¹ * (2 * (μ - ρ) * K + 2 * ρ * K) :=
            mul_le_mul_of_nonneg_left (h3.trans hstep2) h2μinv.le
        _ = K := by field_simp; ring
  have hcontr : ∀ n, ‖yn (n + 1) - y‖ ≤ (ρ / μ) * ‖yn n - y‖ := by
    intro n
    have hdiff : yn (n + 1) - y
        = (2 * μ)⁻¹ • (-(w * (yn n - y)) - (yn n - y) * w) := by
      rw [hstep]
      conv_lhs => rw [hfix]
      rw [← smul_sub]
      congr 1
      simp only [mul_sub, sub_mul]
      abel
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos h2μinv]
    have h1 : ‖-(w * (yn n - y)) - (yn n - y) * w‖ ≤ 2 * ρ * ‖yn n - y‖ := by
      have ha : ‖-(w * (yn n - y))‖ ≤ ρ * ‖yn n - y‖ := by
        rw [norm_neg]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hwn (norm_nonneg _))
      have hb : ‖(yn n - y) * w‖ ≤ ‖yn n - y‖ * ρ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hwn (norm_nonneg _))
      have hc := norm_sub_le (-(w * (yn n - y))) ((yn n - y) * w)
      linarith
    calc (2 * μ)⁻¹ * ‖-(w * (yn n - y)) - (yn n - y) * w‖
        ≤ (2 * μ)⁻¹ * (2 * ρ * ‖yn n - y‖) :=
          mul_le_mul_of_nonneg_left h1 h2μinv.le
      _ = (ρ / μ) * ‖yn n - y‖ := by field_simp
  have hratio0 : 0 ≤ ρ / μ := div_nonneg hρnn hμpos.le
  have hgeo : ∀ n, ‖yn n - y‖ ≤ (ρ / μ) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => rw [hy0]; simp
    | succ n ih =>
      refine (hcontr n).trans ?_
      calc (ρ / μ) * ‖yn n - y‖ ≤ (ρ / μ) * ((ρ / μ) ^ n * ‖y‖) :=
            mul_le_mul_of_nonneg_left ih hratio0
        _ = (ρ / μ) ^ (n + 1) * ‖y‖ := by ring
  have hratio : ρ / μ < 1 := (div_lt_one hμpos).mpr hρμ
  have htend0 : Tendsto (fun n => ‖yn n - y‖) atTop (nhds 0) := by
    refine squeeze_zero (fun n => norm_nonneg _) hgeo ?_
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio).mul_const ‖y‖
    simpa using h
  have hptw : ∀ e : E, Tendsto (fun n => yn n e) atTop (nhds (y e)) := by
    intro e
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n => ‖yn n - y‖ * ‖e‖) (fun n => norm_nonneg _)
      (fun n => ?_) ?_
    · show ‖yn n e - y e‖ ≤ ‖yn n - y‖ * ‖e‖
      exact (yn n - y).le_opNorm e
    · simpa using htend0.mul_const ‖e‖
  refine isHilbertSchmidt_of_tendsto hHS (C := K ^ 2) (fun n => ?_) hptw
  rw [← sq_hsNorm]
  exact pow_le_pow_left₀ (hsNorm_nonneg _) (hbound n) 2

end GaloisForLFunctions.HTGeometry
