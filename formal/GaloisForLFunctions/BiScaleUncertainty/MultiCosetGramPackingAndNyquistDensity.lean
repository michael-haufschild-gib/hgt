import GaloisForLFunctions.BiScaleUncertainty.AbstractBiScaleSystemAndSchurKreinCoupling
import GaloisForLFunctions.BiScaleUncertainty.DisjointCollarCliqueDivergenceAndTuransProblem
import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearAndMultiplicativeGraphUncertainty

/-!
# Pillar XI: Multi-Coset Gram Packing, Selberg–Bombieri Almost-Orthogonality & Nyquist Compression

This module develops **Pillar XI** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**,
addressing the first core requirement for overcoming **Wall 1** (`docs/reports/wall1.md`):
moving from single dyadic-chain cliques of rank $O(\log N)$ to **multi-coset Nyquist packing at
density $e^y = N$** across the $N$ nodes $\log N < \log(N+1) < \dots < \log(2N)$ in the dyadic
window $[\log N, \log(2N)]$.

## Main Results

### Part A: Selberg–Bombieri Almost-Orthogonal Gram Packing in Abstract Hilbert Space
1. **`inner_sum_self_eq_double_sum` & `norm_sq_sub_linearComb_eq`**:
   Exact Gram quadratic expansion for any finite family $\{e_i\}_{i \in s}$ in a real inner product
   space `(E, ⟪·, ·⟫)`.
2. **`sum_inner_sq_sq_le_norm_sq_mul_gram_quad`**:
   Universal Gram–Cauchy–Schwarz inequality
   $$\left(\sum_{i \in s} \langle e_i, x\rangle^2\right)^2 \;\le\; \|x\|^2 \sum_{i \in s}\sum_{j \in s} \langle e_i, x\rangle\langle e_j, x\rangle\langle e_i, e_j\rangle.$$
3. **`gram_quad_le_of_row_sum_bound` & `abstract_selberg_bombieri_bessel_le`**:
   If the Gram row sums satisfy $\sum_{j \in s} |\langle e_i, e_j\rangle| \le M_{\mathrm{row}}$ for
   all $i \in s$, then for every $x \in E$:
   $$\sum_{i \in s} \langle e_i, x\rangle^2 \;\le\; M_{\mathrm{row}}\,\|x\|^2.$$
4. **`autocorr_almost_orthogonal_bessel_sq_le` & `almost_orthogonal_collar_uniform_sum_ge`**:
   For any $M$-node multi-coset family $\{t_i\}_{i \in s}$ whose correlation row sums satisfy
   $\sum_{j \in s} |h_f(t_i - t_j)| \le (1 + \Delta) h_f(0)$, every collar offset $y \in \mathbb{R}$
   satisfies
   $$\sum_{i \in s} \bigl(h_f(0) - h_f(y - t_i)\bigr) \;\ge\; \left(M - \sqrt{M(1 + \Delta)}\right) h_f(0),$$
   showing that the effective multi-coset Gram rank scales as $M / (1 + \Delta)$.

### Part B: Dyadic-Window Nyquist Packing & Origin-Singularity Absorption on $[\log N, \log(2N)]$
5. **`log_succ_sub_log_pos` & `log_succ_sub_log_le_inv`**:
   The logarithmic Nyquist step at $n \ge 1$ satisfies $0 < \log(n+1) - \log n \le \frac{1}{n}$.
6. **`archLevySinhWeight_ge_nat_on_nyquist_collar`**:
   On the Nyquist collar $(0, \log(n+1) - \log n]$, $\sinh y \le \frac{2n+1}{2n(n+1)} < \frac{1}{n}$
   and $e^{y/2} > 1$, so the archimedean Lévy weight satisfies
   $$(n : \mathbb{R}) \;\le\; \operatorname{archLevySinhWeight}(y).$$
7. **`intervalIntegral_dyadic_log_partition_eq` & `integral_autocorr_sq_dyadic_window_le_sum_collar`**:
   Partitions $[\log N, \log(2N)]$ into the $N$ consecutive Nyquist cells
   $[\log(N+k), \log(N+k+1)]$ ($0 \le k < N$) and applies Krein's increment inequality at each
   grid zero $h_f(\log(N+k)) = 0$:
   $$\int_{\log N}^{\log(2N)} h_f(x)^2\,dx \;\le\; 2 h_f(0) \sum_{k=0}^{N-1} \int_0^{\log(N+k+1) - \log(N+k)} \bigl(h_f(0) - h_f(y)\bigr)\,dy.$$
8. **`integral_autocorr_sq_dyadic_window_le_levy_collar`**:
   The $N$-fold Nyquist multiplicity across $[\log N, \log(2N)]$ is absorbed by the origin
   singularity $\operatorname{archLevySinhWeight}(y) \ge N$, yielding the derivative-free bound
   $$\int_{\log N}^{\log(2N)} h_f(x)^2\,dx \;\le\; 2 h_f(0) \int_0^{\log(N+1) - \log N} \bigl(h_f(0) - h_f(y)\bigr)\,\operatorname{archLevySinhWeight}(y)\,dy \;\le\; 2 h_f(0)\,\operatorname{biScaleLevyEnergy}(f).$$
-/

namespace GaloisForLFunctions.BiScaleUncertainty

open MeasureTheory Set Filter
open scoped RealInnerProductSpace BigOperators

noncomputable section

/-! ## §1. Selberg–Bombieri Almost-Orthogonal Gram Packing in Abstract Hilbert Space -/

section AbstractHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [DecidableEq ι]

/-- Double-sum expansion of the squared norm / self-inner-product of a linear combination
`∑ i ∈ s, c i • e i`. -/
theorem inner_sum_self_eq_double_sum (s : Finset ι) (e : ι → E) (c : ι → ℝ) :
    ⟪∑ i ∈ s, c i • e i, ∑ j ∈ s, c j • e j⟫ =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * ⟪e i, e j⟫ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- **Exact Gram Residual Identity:**
`‖x - ∑ i ∈ s, c i • e i‖² = ‖x‖² - 2 ∑ c_i ⟪e_i, x⟫ + ∑_{i, j} c_i c_j ⟪e_i, e_j⟫`. -/
theorem norm_sq_sub_linearComb_eq (s : Finset ι) (e : ι → E) (c : ι → ℝ) (x : E) :
    ‖x - ∑ i ∈ s, c i • e i‖ ^ 2 =
      ‖x‖ ^ 2 - 2 * ∑ i ∈ s, c i * ⟪e i, x⟫ +
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * ⟪e i, e j⟫ := by
  rw [norm_sub_sq_real, real_inner_self_eq_norm_mul_norm,
    ← sq, inner_sum_self_eq_double_sum, inner_sum]
  have hlin : (∑ i ∈ s, ⟪x, c i • e i⟫) = ∑ i ∈ s, c i * ⟪e i, x⟫ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, real_inner_comm]
  linarith

/-- **Universal Gram–Cauchy–Schwarz Inequality:**
For any finite family `{e_i}_{i ∈ s}` in `E` and any `x ∈ E`,
`(∑ i ∈ s, ⟪e_i, x⟫²)² ≤ ‖x‖² * ∑_{i ∈ s} ∑_{j ∈ s} ⟪e_i, x⟫ ⟪e_j, x⟫ ⟪e_i, e_j⟫`. -/
theorem sum_inner_sq_sq_le_norm_sq_mul_gram_quad (s : Finset ι) (e : ι → E) (x : E) :
    (∑ i ∈ s, ⟪e i, x⟫ ^ 2) ^ 2 ≤
      ‖x‖ ^ 2 * ∑ i ∈ s, ∑ j ∈ s, ⟪e i, x⟫ * ⟪e j, x⟫ * ⟪e i, e j⟫ := by
  set v : E := ∑ i ∈ s, ⟪e i, x⟫ • e i
  have hxv : ⟪x, v⟫ = ∑ i ∈ s, ⟪e i, x⟫ ^ 2 := by
    dsimp [v]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, real_inner_comm, sq]
  have hvv : ‖v‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, ⟪e i, x⟫ * ⟪e j, x⟫ * ⟪e i, e j⟫ := by
    rw [sq, ← real_inner_self_eq_norm_mul_norm]
    exact inner_sum_self_eq_double_sum s e (fun i => ⟪e i, x⟫)
  have hcs := abs_real_inner_le_norm x v
  have hsq : ⟪x, v⟫ ^ 2 ≤ (‖x‖ * ‖v‖) ^ 2 := by
    rw [← sq_abs ⟪x, v⟫]
    exact sq_le_sq.mpr (by rw [abs_abs, abs_of_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg v))]; exact hcs)
  rw [hxv, mul_pow, hvv] at hsq
  exact hsq

/-- **Symmetric Geršgorin / Selberg–Bombieri Quadratic Form Bound:**
If every row of the Gram matrix `{⟪e_i, e_j⟫}_{i, j ∈ s}` has absolute sum at most `M_row`, then
for every coefficient vector `c : ι → ℝ`,
`∑_{i ∈ s} ∑_{j ∈ s} c_i c_j ⟪e_i, e_j⟫ ≤ M_row * ∑_{i ∈ s} c_i²`. -/
theorem gram_quad_le_of_row_sum_bound (s : Finset ι) (e : ι → E) (c : ι → ℝ) {M_row : ℝ}
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |⟪e i, e j⟫| ≤ M_row) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * ⟪e i, e j⟫ ≤ M_row * ∑ i ∈ s, (c i) ^ 2 := by
  have hpt : ∀ i ∈ s, ∀ j ∈ s,
      2 * (c i * c j * ⟪e i, e j⟫) ≤ ((c i) ^ 2 + (c j) ^ 2) * |⟪e i, e j⟫| := by
    intro i _ j _
    have h1 : c i * c j * ⟪e i, e j⟫ ≤ |c i * c j * ⟪e i, e j⟫| := le_abs_self _
    rw [abs_mul, abs_mul] at h1
    have h2 : 2 * (|c i| * |c j|) ≤ (c i) ^ 2 + (c j) ^ 2 := by
      have hsq : 0 ≤ (|c i| - |c j|) ^ 2 := sq_nonneg _
      have hci : |c i| ^ 2 = (c i) ^ 2 := sq_abs (c i)
      have hcj : |c j| ^ 2 = (c j) ^ 2 := sq_abs (c j)
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg ⟪e i, e j⟫)
    linarith
  have hsum2 :
      2 * ∑ i ∈ s, ∑ j ∈ s, c i * c j * ⟪e i, e j⟫ ≤
        ∑ i ∈ s, ∑ j ∈ s, ((c i) ^ 2 + (c j) ^ 2) * |⟪e i, e j⟫| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => hpt i hi j hj
  have hsymm :
      (∑ i ∈ s, ∑ j ∈ s, (c j) ^ 2 * |⟪e i, e j⟫|) =
        ∑ i ∈ s, ∑ j ∈ s, (c i) ^ 2 * |⟪e i, e j⟫| := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm]
  have hsplit :
      (∑ i ∈ s, ∑ j ∈ s, ((c i) ^ 2 + (c j) ^ 2) * |⟪e i, e j⟫|) =
        2 * ∑ i ∈ s, (c i) ^ 2 * ∑ j ∈ s, |⟪e i, e j⟫| := by
    have h1 :
        (∑ i ∈ s, ∑ j ∈ s, ((c i) ^ 2 + (c j) ^ 2) * |⟪e i, e j⟫|) =
          (∑ i ∈ s, ∑ j ∈ s, (c i) ^ 2 * |⟪e i, e j⟫|) +
            ∑ i ∈ s, ∑ j ∈ s, (c j) ^ 2 * |⟪e i, e j⟫| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => add_mul _ _ _
    rw [h1, hsymm, ← two_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hrow_sum :
      ∑ i ∈ s, (c i) ^ 2 * ∑ j ∈ s, |⟪e i, e j⟫| ≤ M_row * ∑ i ∈ s, (c i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    calc
      (c i) ^ 2 * ∑ j ∈ s, |⟪e i, e j⟫| ≤ (c i) ^ 2 * M_row :=
        mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
      _ = M_row * (c i) ^ 2 := mul_comm _ _
  linarith

/-- **Selberg–Bombieri Almost-Orthogonal Bessel Inequality:**
If `0 ≤ M_row` and `∑_{j ∈ s} |⟪e_i, e_j⟫| ≤ M_row` for all `i ∈ s`, then for every `x ∈ E`,
`∑_{i ∈ s} ⟪e_i, x⟫² ≤ M_row * ‖x‖²`. -/
theorem abstract_selberg_bombieri_bessel_le (s : Finset ι) (e : ι → E) (x : E) {M_row : ℝ}
    (hM_nonneg : 0 ≤ M_row)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |⟪e i, e j⟫| ≤ M_row) :
    ∑ i ∈ s, ⟪e i, x⟫ ^ 2 ≤ M_row * ‖x‖ ^ 2 := by
  set S := ∑ i ∈ s, ⟪e i, x⟫ ^ 2
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases eq_or_lt_of_le hS_nonneg with hS0 | hS_pos
  · rw [← hS0]
    exact mul_nonneg hM_nonneg (sq_nonneg _)
  · have hcs := sum_inner_sq_sq_le_norm_sq_mul_gram_quad s e x
    have hq := gram_quad_le_of_row_sum_bound s e (fun i => ⟪e i, x⟫) hrow
    have hprod :
        S ^ 2 ≤ ‖x‖ ^ 2 * (M_row * S) :=
      le_trans hcs (mul_le_mul_of_nonneg_left hq (sq_nonneg ‖x‖))
    have hcancel : S * S ≤ (M_row * ‖x‖ ^ 2) * S := by
      calc
        S * S = S ^ 2 := (sq S).symm
        _ ≤ ‖x‖ ^ 2 * (M_row * S) := hprod
        _ = (M_row * ‖x‖ ^ 2) * S := by ring
    exact le_of_mul_le_mul_right hcancel hS_pos

end AbstractHilbert

/-! ## §2. Almost-Orthogonal Multi-Coset Collar Bounds for Autocorrelations -/

section AlmostOrthogonalAutocorr

variable {ι : Type*} [DecidableEq ι]

/-- **Multi-Coset Selberg–Bombieri Sphere Bound for Autocorrelations:**
If `{t_i}_{i ∈ s}` is a finite node family whose correlation row sums satisfy
`∑_{j ∈ s} |autocorr f (t_i - t_j)| ≤ (1 + Δ) * autocorr f 0` with `0 ≤ 1 + Δ`, then for every
collar offset `y ∈ ℝ`:
`∑_{i ∈ s} (autocorr f (y - t_i))² ≤ (1 + Δ) * (autocorr f 0)²`. -/
theorem autocorr_almost_orthogonal_bessel_sq_le {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ) {Δ : ℝ} (hΔ : 0 ≤ 1 + Δ)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |autocorr f (t i - t j)| ≤ (1 + Δ) * autocorr f 0) (y : ℝ) :
    ∑ i ∈ s, (autocorr f (y - t i)) ^ 2 ≤ (1 + Δ) * (autocorr f 0) ^ 2 := by
  set A := (1 + Δ) * autocorr f 0
  set S := ∑ i ∈ s, (autocorr f (y - t i)) ^ 2
  have h0_nonneg : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hA_nonneg : 0 ≤ A := mul_nonneg hΔ h0_nonneg
  rcases eq_or_lt_of_le hA_nonneg with hA0 | hA_pos
  · have hS0 : S = 0 := by
      rcases mul_eq_zero.mp hA0.symm with hΔ0 | hf0
      · rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
        · simp [S]
        · have hrow0 : ∑ j ∈ s, |autocorr f (t i₀ - t j)| ≤ 0 := by
            have := hrow i₀ hi₀
            linarith
          have hself0 : |autocorr f (t i₀ - t i₀)| ≤ 0 :=
            le_trans (Finset.single_le_sum (fun j _ => abs_nonneg _) hi₀) hrow0
          have hf0 : autocorr f 0 = 0 := by
            rw [sub_self] at hself0
            exact le_antisymm (le_trans (le_abs_self _) hself0) h0_nonneg
          refine Finset.sum_eq_zero fun i _ => ?_
          have habs := abs_autocorr_le_zero hfc hf (y - t i)
          rw [hf0] at habs
          have : autocorr f (y - t i) = 0 := abs_nonpos_iff.mp habs
          simp [this]
      · refine Finset.sum_eq_zero fun i _ => ?_
        have habs := abs_autocorr_le_zero hfc hf (y - t i)
        rw [hf0] at habs
        have : autocorr f (y - t i) = 0 := abs_nonpos_iff.mp habs
        simp [this]
    rw [hS0]
    exact mul_nonneg hΔ (sq_nonneg _)
  · set c : ι → ℝ := fun i => autocorr f (y - t i)
    have hgram_nonneg :
        0 ≤ A ^ 2 * autocorr f 0 - 2 * A * S +
          ∑ i ∈ s, ∑ j ∈ s, c i * c j * autocorr f (t i - t j) := by
      have hint :
          0 ≤ ∫ u : ℝ, (A * f (u + y) - ∑ i ∈ s, c i * f (u + t i)) ^ 2 :=
        integral_nonneg fun u => sq_nonneg _
      have hexp :
          (∫ u : ℝ, (A * f (u + y) - ∑ i ∈ s, c i * f (u + t i)) ^ 2) =
            A ^ 2 * autocorr f 0 - 2 * A * S +
              ∑ i ∈ s, ∑ j ∈ s, c i * c j * autocorr f (t i - t j) := by
        have h1 :
            (fun u : ℝ => (A * f (u + y) - ∑ i ∈ s, c i * f (u + t i)) ^ 2) =
              fun u : ℝ =>
                A ^ 2 * (f (u + y)) ^ 2 -
                  2 * A * (∑ i ∈ s, c i * (f (u + y) * f (u + t i))) +
                  ∑ i ∈ s, ∑ j ∈ s, c i * c j * (f (u + t i) * f (u + t j)) := by
          ext u
          have hsub :
              (A * f (u + y) - ∑ i ∈ s, c i * f (u + t i)) ^ 2 =
                A ^ 2 * (f (u + y)) ^ 2 -
                  2 * A * (f (u + y) * ∑ i ∈ s, c i * f (u + t i)) +
                  (∑ i ∈ s, c i * f (u + t i)) * (∑ j ∈ s, c j * f (u + t j)) := by
            ring
          rw [hsub, Finset.mul_sum]
          have hcross :
              (∑ i ∈ s, f (u + y) * (c i * f (u + t i))) =
                ∑ i ∈ s, c i * (f (u + y) * f (u + t i)) :=
            Finset.sum_congr rfl fun i _ => by ring
          have hquad :
              (∑ i ∈ s, c i * f (u + t i)) * (∑ j ∈ s, c j * f (u + t j)) =
                ∑ i ∈ s, ∑ j ∈ s, c i * c j * (f (u + t i) * f (u + t j)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
          rw [hcross, hquad]
        have hf_shift : ∀ a : ℝ, Continuous (fun u => f (u + a)) :=
          fun a => hf.comp (continuous_id.add continuous_const)
        have hfc_shift : ∀ a : ℝ, HasCompactSupport (fun u => f (u + a)) :=
          fun a => hfc.comp_homeomorph (Homeomorph.addRight a)
        have hint_sq : Integrable (fun u => A ^ 2 * (f (u + y)) ^ 2) := by
          have := ((hf_shift y).mul (hf_shift y)).integrable_of_hasCompactSupport
            ((hfc_shift y).mul_left)
          simpa only [sq] using this.const_mul (A ^ 2)
        have hint_cross_i : ∀ i ∈ s,
            Integrable (fun u => c i * (f (u + y) * f (u + t i))) := fun i _ =>
          (((hf_shift y).mul (hf_shift (t i))).integrable_of_hasCompactSupport
            ((hfc_shift y).mul_left)).const_mul (c i)
        have hint_cross :
            Integrable (fun u => 2 * A * ∑ i ∈ s, c i * (f (u + y) * f (u + t i))) :=
          (integrable_finset_sum s hint_cross_i).const_mul (2 * A)
        have hint_quad_ij : ∀ i ∈ s, ∀ j ∈ s,
            Integrable (fun u => c i * c j * (f (u + t i) * f (u + t j))) := fun i _ j _ =>
          (((hf_shift (t i)).mul (hf_shift (t j))).integrable_of_hasCompactSupport
            ((hfc_shift (t i)).mul_left)).const_mul (c i * c j)
        have hint_quad :
            Integrable (fun u =>
              ∑ i ∈ s, ∑ j ∈ s, c i * c j * (f (u + t i) * f (u + t j))) :=
          integrable_finset_sum s fun i hi => integrable_finset_sum s (hint_quad_ij i hi)
        rw [h1, integral_add (hint_sq.sub hint_cross) hint_quad,
          integral_sub hint_sq hint_cross, integral_const_mul, integral_const_mul,
          integral_finset_sum s hint_cross_i,
          integral_finset_sum s fun i hi => integrable_finset_sum s (hint_quad_ij i hi)]
        have h0 : (∫ u : ℝ, (f (u + y)) ^ 2) = autocorr f 0 := by
          have := MeasureTheory.integral_add_right_eq_self (fun u : ℝ => (f u) ^ 2) y
          rw [this]
          unfold autocorr
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          simp [sq]
        have hci : ∀ i ∈ s,
            (∫ u : ℝ, c i * (f (u + y) * f (u + t i))) = (c i) ^ 2 := by
          intro i _
          rw [integral_const_mul]
          have htr := MeasureTheory.integral_add_right_eq_self
            (fun u : ℝ => f (u + (y - t i)) * f u) (t i)
          have h2 :
              (∫ u : ℝ, f (u + y) * f (u + t i)) = autocorr f (y - t i) := by
            rw [← htr]
            unfold autocorr
            refine integral_congr_ae (Eventually.of_forall fun u => ?_)
            dsimp
            have : u + t i + (y - t i) = u + y := by ring
            rw [this, mul_comm]
          rw [h2]
          dsimp [c]
          ring
        have hcij : ∀ i ∈ s, ∀ j ∈ s,
            (∫ u : ℝ, c i * c j * (f (u + t i) * f (u + t j))) =
              c i * c j * autocorr f (t i - t j) := by
          intro i _ j _
          rw [integral_const_mul]
          congr 1
          have htr := MeasureTheory.integral_add_right_eq_self
            (fun u : ℝ => f (u + (t i - t j)) * f u) (t j)
          rw [← htr]
          unfold autocorr
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          dsimp
          have : u + t j + (t i - t j) = u + t i := by ring
          rw [this, mul_comm]
        rw [h0, Finset.sum_congr rfl hci]
        have hquad_eval :
            (∑ i ∈ s, ∫ u : ℝ, ∑ j ∈ s, c i * c j * (f (u + t i) * f (u + t j))) =
              ∑ i ∈ s, ∑ j ∈ s, c i * c j * autocorr f (t i - t j) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [integral_finset_sum s (hint_quad_ij i hi)]
          exact Finset.sum_congr rfl (hcij i hi)
        rw [hquad_eval]
      linarith
    have hpt : ∀ i ∈ s, ∀ j ∈ s,
        2 * (c i * c j * autocorr f (t i - t j)) ≤
          ((c i) ^ 2 + (c j) ^ 2) * |autocorr f (t i - t j)| := by
      intro i _ j _
      have h1 : c i * c j * autocorr f (t i - t j) ≤
          |c i * c j * autocorr f (t i - t j)| := le_abs_self _
      rw [abs_mul, abs_mul] at h1
      have h2 : 2 * (|c i| * |c j|) ≤ (c i) ^ 2 + (c j) ^ 2 := by
        have hsq : 0 ≤ (|c i| - |c j|) ^ 2 := sq_nonneg _
        have hci : |c i| ^ 2 = (c i) ^ 2 := sq_abs (c i)
        have hcj : |c j| ^ 2 = (c j) ^ 2 := sq_abs (c j)
        linarith
      have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (autocorr f (t i - t j)))
      linarith
    have hsum2 :
        2 * ∑ i ∈ s, ∑ j ∈ s, c i * c j * autocorr f (t i - t j) ≤
          ∑ i ∈ s, ∑ j ∈ s, ((c i) ^ 2 + (c j) ^ 2) * |autocorr f (t i - t j)| := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => hpt i hi j hj
    have hsymm :
        (∑ i ∈ s, ∑ j ∈ s, (c j) ^ 2 * |autocorr f (t i - t j)|) =
          ∑ i ∈ s, ∑ j ∈ s, (c i) ^ 2 * |autocorr f (t i - t j)| := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      have hev : t i - t j = -(t j - t i) := by ring
      rw [hev, autocorr_neg]
    have hsplit :
        (∑ i ∈ s, ∑ j ∈ s, ((c i) ^ 2 + (c j) ^ 2) * |autocorr f (t i - t j)|) =
          2 * ∑ i ∈ s, (c i) ^ 2 * ∑ j ∈ s, |autocorr f (t i - t j)| := by
    have h1 :
        (∑ i ∈ s, ∑ j ∈ s, ((c i) ^ 2 + (c j) ^ 2) * |autocorr f (t i - t j)|) =
          (∑ i ∈ s, ∑ j ∈ s, (c i) ^ 2 * |autocorr f (t i - t j)|) +
            ∑ i ∈ s, ∑ j ∈ s, (c j) ^ 2 * |autocorr f (t i - t j)| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => add_mul _ _ _
    rw [h1, hsymm, ← two_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    have hrow_sum :
        ∑ i ∈ s, (c i) ^ 2 * ∑ j ∈ s, |autocorr f (t i - t j)| ≤ A * S := by
      dsimp [S, c, A]
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      calc
        (autocorr f (y - t i)) ^ 2 * ∑ j ∈ s, |autocorr f (t i - t j)| ≤
            (autocorr f (y - t i)) ^ 2 * ((1 + Δ) * autocorr f 0) :=
          mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
        _ = ((1 + Δ) * autocorr f 0) * (autocorr f (y - t i)) ^ 2 := mul_comm _ _
    have hquad_le :
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * autocorr f (t i - t j) ≤ A * S := by
      linarith
    have hAS : S * A ≤ ((1 + Δ) * (autocorr f 0) ^ 2) * A := by
      have : A * S ≤ A ^ 2 * autocorr f 0 := by linarith
      calc
        S * A = A * S := mul_comm _ _
        _ ≤ A ^ 2 * autocorr f 0 := this
        _ = ((1 + Δ) * (autocorr f 0) ^ 2) * A := by dsimp [A]; ring
    exact le_of_mul_le_mul_right hAS hA_pos

/-- **Almost-Orthogonal Multi-Coset Collar Amplification Law:**
If `{t_i}_{i ∈ s}` is an `M`-node multi-coset family (`M = s.card`) whose correlation row sums
satisfy `∑_{j ∈ s} |autocorr f (t_i - t_j)| ≤ (1 + Δ) * autocorr f 0` (`0 ≤ 1 + Δ`), then for every
collar offset `y ∈ ℝ`:
`((s.card : ℝ) - √((s.card : ℝ) * (1 + Δ))) * autocorr f 0 ≤ ∑_{i ∈ s} (autocorr f 0 - autocorr f (y - t_i))`. -/
theorem almost_orthogonal_collar_uniform_sum_ge {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ) {Δ : ℝ} (hΔ : 0 ≤ 1 + Δ)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |autocorr f (t i - t j)| ≤ (1 + Δ) * autocorr f 0) (y : ℝ) :
    ((s.card : ℝ) - Real.sqrt ((s.card : ℝ) * (1 + Δ))) * autocorr f 0 ≤
      ∑ i ∈ s, (autocorr f 0 - autocorr f (y - t i)) := by
  have hbessel := autocorr_almost_orthogonal_bessel_sq_le hfc hf s t hΔ hrow y
  have hcs := sq_sum_le_card_mul_sum_sq s (fun i => autocorr f (y - t i))
  have hcard_nonneg : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg s.card
  have h0_nonneg : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hsum_sq_le :
      (∑ i ∈ s, autocorr f (y - t i)) ^ 2 ≤
        (Real.sqrt ((s.card : ℝ) * (1 + Δ)) * autocorr f 0) ^ 2 := by
    calc
      (∑ i ∈ s, autocorr f (y - t i)) ^ 2 ≤
          (s.card : ℝ) * ∑ i ∈ s, (autocorr f (y - t i)) ^ 2 := hcs
      _ ≤ (s.card : ℝ) * ((1 + Δ) * (autocorr f 0) ^ 2) :=
          mul_le_mul_of_nonneg_left hbessel hcard_nonneg
      _ = ((s.card : ℝ) * (1 + Δ)) * (autocorr f 0) ^ 2 := by ring
      _ = (Real.sqrt ((s.card : ℝ) * (1 + Δ))) ^ 2 * (autocorr f 0) ^ 2 := by
          rw [Real.sq_sqrt (mul_nonneg hcard_nonneg hΔ)]
      _ = (Real.sqrt ((s.card : ℝ) * (1 + Δ)) * autocorr f 0) ^ 2 := by ring
  have hsum_le :
      ∑ i ∈ s, autocorr f (y - t i) ≤
        Real.sqrt ((s.card : ℝ) * (1 + Δ)) * autocorr f 0 := by
    have habs := abs_le_of_sq_le_sq' hsum_sq_le
      (mul_nonneg (Real.sqrt_nonneg _) h0_nonneg)
    exact habs.2
  have hsplit :
      (∑ i ∈ s, (autocorr f 0 - autocorr f (y - t i))) =
        (s.card : ℝ) * autocorr f 0 - ∑ i ∈ s, autocorr f (y - t i) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

end AlmostOrthogonalAutocorr

/-! ## §3. Dyadic-Window Nyquist Packing & Origin-Singularity Absorption on `[log N, log(2N)]` -/

/-- The logarithmic Nyquist step `log(n + 1) - log n` is strictly positive for `n ≥ 1`. -/
theorem log_succ_sub_log_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr ( Nat.pos_of_ne_zero (by omega))
  have hlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact sub_pos.mpr (Real.log_lt_log hn_pos hlt)

/-- **Logarithmic Nyquist Step Upper Bound:**
For every `n ≥ 1`, `log(n + 1) - log n ≤ 1 / n`. -/
theorem log_succ_sub_log_le_inv {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [← Real.log_div hn1_pos.ne' hn_pos.ne']
  have hdiv_pos : 0 < ((n + 1 : ℕ) : ℝ) / (n : ℝ) := div_pos hn1_pos hn_pos
  have hlog := Real.log_le_sub_one_of_pos hdiv_pos
  have hsub : ((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
    push_cast
    field_simp [hn_pos.ne']
    ring
  linarith

/-- For `N ≤ n`, the Nyquist step `log(n + 1) - log n` is at most `log(N + 1) - log N`. -/
theorem log_succ_sub_log_antitone {N n : ℕ} (hN : 1 ≤ N) (hNn : N ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤
      Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN1_pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [← Real.log_div hn1_pos.ne' hn_pos.ne', ← Real.log_div hN1_pos.ne' hN_pos.ne']
  refine Real.log_le_log (div_pos hn1_pos hn_pos) ?_
  have hle : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hNn
  rw [div_le_div_iff₀ hn_pos hN_pos]
  push_cast
  linarith

/-- **Origin-Singularity Absorption on the Nyquist Collar:**
For every `n ≥ 1` and `y ∈ (0, log(n + 1) - log n]`,
`sinh y < 1 / n` and `(n : ℝ) ≤ archLevySinhWeight y`. -/
theorem archLevySinhWeight_ge_nat_on_nyquist_collar {n : ℕ} (hn : 1 ≤ n) {y : ℝ}
    (hy_pos : 0 < y) (hy_le : y ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) :
    (n : ℝ) ≤ archLevySinhWeight y := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set δ := Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)
  have hexp_δ : Real.exp δ = ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    dsimp [δ]
    rw [Real.exp_sub, Real.exp_log hn1_pos, Real.exp_log hn_pos]
  have hexp_neg_δ : Real.exp (-δ) = (n : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    rw [Real.exp_neg, hexp_δ, inv_div]
  have hsinh_δ : Real.sinh δ < 1 / (n : ℝ) := by
    rw [Real.sinh_eq, hexp_δ, hexp_neg_δ]
    have hdiff :
        (((n + 1 : ℕ) : ℝ) / (n : ℝ) - (n : ℝ) / ((n + 1 : ℕ) : ℝ)) / 2 =
          (2 * (n : ℝ) + 1) / (2 * (n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
      push_cast
      field_simp [hn_pos.ne', hn1_pos.ne']
      ring
    rw [hdiff, div_lt_div_iff₀ (by positivity) hn_pos]
    push_cast
    nlinarith
  have hsinh_y_le : Real.sinh y ≤ Real.sinh δ := Real.sinh_le_sinh.mpr hy_le
  have hsinh_y_lt : Real.sinh y < 1 / (n : ℝ) := lt_of_le_of_lt hsinh_y_le hsinh_δ
  have hsinh_y_pos : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy_pos
  have hexp_half_gt : 1 < Real.exp (y / 2) := Real.one_lt_exp_iff.mpr (half_pos hy_pos)
  rw [archLevySinhWeight_of_pos hy_pos]
  rw [le_div_iff₀ hsinh_y_pos]
  have hmul : (n : ℝ) * Real.sinh y < 1 := by
    have := mul_lt_mul_of_pos_left hsinh_y_lt hn_pos
    rwa [mul_one_div_cancel hn_pos.ne'] at this
  linarith

/-- **Logarithmic Grid Partition Identity:**
For any continuous function `F : ℝ → ℝ` and `N ≥ 1`, `K : ℕ`,
`∫ x in log N..log(N + K), F x = ∑ k ∈ range K, ∫ y in 0..(log(N + k + 1) - log(N + k)), F (log(N + k) + y)`. -/
theorem intervalIntegral_log_grid_partition_eq {F : ℝ → ℝ} (hF : Continuous F)
    (N : ℕ) (K : ℕ) :
    (∫ x in Real.log (N : ℝ)..Real.log ((N + K : ℕ) : ℝ), F x) =
      ∑ k ∈ Finset.range K,
        ∫ y in (0 : ℝ)..(Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)),
          F (Real.log ((N + k : ℕ) : ℝ) + y) := by
  induction K with
  | zero =>
    simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h1 : IntervalIntegrable F volume (Real.log (N : ℝ)) (Real.log ((N + K : ℕ) : ℝ)) :=
      hF.intervalIntegrable _ _
    have h2 :
        IntervalIntegrable F volume (Real.log ((N + K : ℕ) : ℝ))
          (Real.log ((N + (K + 1) : ℕ) : ℝ)) :=
      hF.intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
    congr 1
    have hshift :=
      intervalIntegral_collar_shift F (Real.log ((N + K : ℕ) : ℝ))
        (Real.log ((N + K + 1 : ℕ) : ℝ) - Real.log ((N + K : ℕ) : ℝ))
    have hadd :
        Real.log ((N + K : ℕ) : ℝ) +
          (Real.log ((N + K + 1 : ℕ) : ℝ) - Real.log ((N + K : ℕ) : ℝ)) =
          Real.log ((N + (K + 1) : ℕ) : ℝ) := by
      have hnat : N + K + 1 = N + (K + 1) := by omega
      rw [hnat]
      ring
    rw [hadd] at hshift
    exact hshift.symm

/-- **Dyadic-Window Logarithmic Partition Identity (`[log N, log(2N)]`):**
For any continuous function `F : ℝ → ℝ` and `N : ℕ`,
`∫ x in log N..log(2 * N), F x = ∑ k ∈ range N, ∫ y in 0..(log(N + k + 1) - log(N + k)), F (log(N + k) + y)`. -/
theorem intervalIntegral_dyadic_log_partition_eq {F : ℝ → ℝ} (hF : Continuous F) (N : ℕ) :
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), F x) =
      ∑ k ∈ Finset.range N,
        ∫ y in (0 : ℝ)..(Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)),
          F (Real.log ((N + k : ℕ) : ℝ) + y) := by
  rw [two_mul N]
  exact intervalIntegral_log_grid_partition_eq hF N N

/-- **Krein Nyquist-Compression Inequality on the Dyadic Window `[log N, log(2N)]`:**
If `f ∈ C_c(ℝ)` satisfies `autocorr f (log(N + k)) = 0` for all `0 ≤ k < N` (`N ≥ 1`), then
`∫ x in log N..log(2N), (autocorr f x)² ≤ 2 * autocorr f 0 * ∑ k ∈ range N, ∫ y in 0..(log(N + k + 1) - log(N + k)), (autocorr f 0 - autocorr f y)`. -/
theorem integral_autocorr_sq_dyadic_window_le_sum_collar {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) {N : ℕ} (hN : 1 ≤ N)
    (hzeros : ∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0) :
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (autocorr f x) ^ 2) ≤
      2 * autocorr f 0 *
        ∑ k ∈ Finset.range N,
          ∫ y in (0 : ℝ)..(Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)),
            (autocorr f 0 - autocorr f y) := by
  have hc : Continuous (autocorr f) := continuous_autocorr_of_continuous hfc hf
  rw [intervalIntegral_dyadic_log_partition_eq (hc.pow 2) N, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  set δ_k := Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)
  have hNk : 1 ≤ N + k := by omega
  have hδ_pos : 0 < δ_k := log_succ_sub_log_pos hNk
  rw [← intervalIntegral.integral_const_mul]
  have hint1 :
      IntervalIntegrable (fun y => (autocorr f (Real.log ((N + k : ℕ) : ℝ) + y)) ^ 2)
        volume 0 δ_k :=
    ((hc.comp (continuous_const.add continuous_id)).pow 2).intervalIntegrable _ _
  have hint2 :
      IntervalIntegrable (fun y => 2 * autocorr f 0 * (autocorr f 0 - autocorr f y))
        volume 0 δ_k :=
    (continuous_const.mul (continuous_const.sub hc)).intervalIntegrable _ _
  refine intervalIntegral.integral_mono_on hδ_pos.le hint1 hint2 fun y _ => ?_
  have hkrein :=
    autocorr_sq_le_two_mul_sub_of_zero hfc hf (hzeros k hk)
      (Real.log ((N + k : ℕ) : ℝ) + y)
  have hdiff : Real.log ((N + k : ℕ) : ℝ) + y - Real.log ((N + k : ℕ) : ℝ) = y := by ring
  rw [hdiff] at hkrein
  exact hkrein

/-- **Derivative-Free Nyquist `L²` Compression via Origin-Singularity Absorption:**
If `f ∈ C²_c(ℝ)` satisfies `autocorr f (log(N + k)) = 0` for all `0 ≤ k < N` (`N ≥ 1`), then the
`N`-fold multiplicity of the `N` Nyquist cells in `[log N, log(2N)]` is absorbed by the origin
singularity `archLevySinhWeight y ≥ N` on `(0, log(N + 1) - log N]`, yielding:
`∫ x in log N..log(2N), (autocorr f x)² ≤ 2 * autocorr f 0 * ∫ y in Ioc 0 (log(N + 1) - log N), (autocorr f 0 - autocorr f y) * archLevySinhWeight y ≤ 2 * autocorr f 0 * biScaleLevyEnergy f`. -/
theorem integral_autocorr_sq_dyadic_window_le_levy_collar {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N)
    (hzeros : ∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0) :
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (autocorr f x) ^ 2) ≤
      2 * autocorr f 0 *
        ∫ y in Ioc 0 (Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)),
          (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
  have hbase := integral_autocorr_sq_dyadic_window_le_sum_collar hfc hf.continuous hN hzeros
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  set δ_N := Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ)
  have hδN_pos : 0 < δ_N := log_succ_sub_log_pos hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hint_levy :
      IntegrableOn (fun y => (autocorr f 0 - autocorr f y) * archLevySinhWeight y)
        (Ioc 0 δ_N) :=
    (integrableOn_biScaleLevyIntegrand hf hfc).mono_set (fun y hy => hy.1)
  have hk_le : ∀ k ∈ Finset.range N,
      (∫ y in (0 : ℝ)..(Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)),
        (autocorr f 0 - autocorr f y)) ≤
        (1 / (N : ℝ)) *
          ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    intro k _
    set δ_k := Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)
    have hNk : 1 ≤ N + k := by omega
    have hδk_pos : 0 < δ_k := log_succ_sub_log_pos hNk
    have hδk_le_δN : δ_k ≤ δ_N := log_succ_sub_log_antitone hN (by omega)
    rw [intervalIntegral.integral_of_le hδk_pos.le]
    have hsub_mono :
        (∫ y in Ioc 0 δ_k, (autocorr f 0 - autocorr f y)) ≤
          ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) := by
      refine setIntegral_mono_set
        ((continuous_const.sub hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self) ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y _
        exact autocorr_sub_nonneg hfc hf.continuous y
      · refine Eventually.of_forall fun y hy => ⟨hy.1, le_trans hy.2 hδk_le_δN⟩
    have hweight_mono :
        (∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y)) ≤
          (1 / (N : ℝ)) *
            ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
      rw [← integral_const_mul]
      refine setIntegral_mono_ae_restrict
        ((continuous_const.sub hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (hint_levy.const_mul (1 / (N : ℝ))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      have hge : (N : ℝ) ≤ archLevySinhWeight y :=
        archLevySinhWeight_ge_nat_on_nyquist_collar hN hy.1 hy.2
      have h1 : 1 ≤ (1 / (N : ℝ)) * archLevySinhWeight y := by
        rw [one_div_mul_eq_div, one_le_div hN_pos]
        exact hge
      have hnonneg : 0 ≤ autocorr f 0 - autocorr f y :=
        autocorr_sub_nonneg hfc hf.continuous y
      calc
        autocorr f 0 - autocorr f y = (autocorr f 0 - autocorr f y) * 1 := (mul_one _).symm
        _ ≤ (autocorr f 0 - autocorr f y) * ((1 / (N : ℝ)) * archLevySinhWeight y) :=
          mul_le_mul_of_nonneg_left h1 hnonneg
        _ = (1 / (N : ℝ)) * ((autocorr f 0 - autocorr f y) * archLevySinhWeight y) := by ring
    exact le_trans hsub_mono hweight_mono
  have hsum_le :
      (∑ k ∈ Finset.range N,
        ∫ y in (0 : ℝ)..(Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)),
          (autocorr f 0 - autocorr f y)) ≤
        ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
    calc
      (∑ k ∈ Finset.range N,
        ∫ y in (0 : ℝ)..(Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)),
          (autocorr f 0 - autocorr f y)) ≤
          ∑ _k ∈ Finset.range N,
            (1 / (N : ℝ)) *
              ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y :=
        Finset.sum_le_sum hk_le
      _ = (N : ℝ) * ((1 / (N : ℝ)) *
            ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∫ y in Ioc 0 δ_N, (autocorr f 0 - autocorr f y) * archLevySinhWeight y := by
        rw [← mul_assoc, mul_one_div_cancel hN_pos.ne', one_mul]
  exact le_trans hbase (mul_le_mul_of_nonneg_left hsum_le (mul_nonneg two_pos.le (autocorr_zero_nonneg f)))

/-- Corollary: Under the dyadic-window zero hypothesis `autocorr f (log(N + k)) = 0` (`0 ≤ k < N`),
`∫ x in log N..log(2N), (autocorr f x)² ≤ 2 * autocorr f 0 * biScaleLevyEnergy f`. -/
theorem integral_autocorr_sq_dyadic_window_le_biScaleLevyEnergy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {N : ℕ} (hN : 1 ≤ N)
    (hzeros : ∀ k ∈ Finset.range N, autocorr f (Real.log ((N + k : ℕ) : ℝ)) = 0) :
    (∫ x in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), (autocorr f x) ^ 2) ≤
      2 * autocorr f 0 * biScaleLevyEnergy f := by
  refine le_trans (integral_autocorr_sq_dyadic_window_le_levy_collar hf hfc hN hzeros) ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg two_pos.le (autocorr_zero_nonneg f))
  unfold biScaleLevyEnergy
  refine setIntegral_mono_set (integrableOn_biScaleLevyIntegrand hf hfc) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous y) (archLevySinhWeight_pos hy).le
  · refine Eventually.of_forall fun y hy => hy.1

end

end GaloisForLFunctions.BiScaleUncertainty
