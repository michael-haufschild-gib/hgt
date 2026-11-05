import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindowsVarySlowlyAtTheirTarget
import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial

/-!
# The image reads the discriminant of a cluster

A cluster of `k` points `a_i = γ_{p_i} − ω` has the moment Hankel matrix
`H(μ)_{ij} = μ_{i+j} = Σ_l a_l^{i+j}` (`i, j < k`), which is `VᵀV` for the Vandermonde matrix `V`.
So `det H(μ) = Π_{i<j}(a_j − a_i)²` is the discriminant of the cluster
(`HTGeometry.det_powerSum_hankel`). The camera reads the moments up to order `2k − 2`
(`discMoment_readout_rvm`). The normalization of the camera cancels from

`D_img = (k/W₀)^k · (Π_{i<k} (−i)^{−i})² · det (W_{i+j})_{i,j<k}`,

so the discriminant of every isolated cluster is read from `2k − 1` window images:

* `norm_det_sub_le`, `norm_det_le` — entrywise perturbation of a `k × k` determinant;
* `det_hankel_scale` — rescaling the Hankel matrix by the cluster radius;
* `imageDiscriminant_eq` — `D_img = (k/m₀)^k det H(m)` for `m_j = W_j/((−i)^j Φ)`;
* `cluster_discriminant_rvm` — uniformly in `T`, `|D_img − Π_{i<j}(γ_{p_j} − γ_{p_i})²|` is at
  most `clusterReadError k r T^{M' + κ_λ} e^{−K' log³(T/2π)}`.

For `k = 2` this is `4(W₁² − W₀W₂)/W₀²` of `TheImageHankelReadsTheSquaredGap`. A cluster is
simple (all points distinct) iff its discriminant is nonzero, and the camera reads that
discriminant at the scale `r^{k(k−1)}` of the cluster.
-/

open MeasureTheory Complex Set Filter Matrix
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-! ### Perturbation of determinants -/

/-- Products of factors bounded by `C ≥ 1` differ by at most `card · C^card · δ`. -/
theorem norm_prod_sub_prod_le_of_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ) {C δ : ℝ}
    (hC : 1 ≤ C) (hδ : 0 ≤ δ) (ha : ∀ i ∈ s, ‖a i‖ ≤ C) (hb : ∀ i ∈ s, ‖b i‖ ≤ C)
    (hd : ∀ i ∈ s, ‖a i - b i‖ ≤ δ) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ s.card * C ^ s.card * δ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    have ha' : ∀ i ∈ s, ‖a i‖ ≤ C := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ C := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ s, ‖a i - b i‖ ≤ δ := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hrec := ih ha' hb' hd'
    have hC0 : 0 ≤ C := by linarith
    have hpb : ‖∏ i ∈ s, b i‖ ≤ C ^ s.card := by
      rw [norm_prod]
      exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) hb').trans_eq
        (Finset.prod_const C)
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
    have e : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i =
        a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hax := ha x (Finset.mem_insert_self x s)
    have hdx := hd x (Finset.mem_insert_self x s)
    have h1 := mul_le_mul hax hrec (norm_nonneg _) hC0
    have h2 := mul_le_mul hdx hpb (norm_nonneg _) hδ
    have hCpow : C ^ s.card ≤ C ^ (s.card + 1) := pow_le_pow_right₀ hC (Nat.le_succ _)
    have e2 : C * (s.card * C ^ s.card * δ) = s.card * C ^ (s.card + 1) * δ := by ring
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hCpow hδ, pow_nonneg hC0 s.card]

/-- **Entrywise perturbation of a determinant.** Entries bounded by `C ≥ 1` and differing by at
most `δ` give `‖det A − det B‖ ≤ k! · k C^k δ`. -/
theorem norm_det_sub_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) {C δ : ℝ} (hC : 1 ≤ C)
    (hδ : 0 ≤ δ) (hA : ∀ i j, ‖A i j‖ ≤ C) (hB : ∀ i j, ‖B i j‖ ≤ C)
    (hAB : ∀ i j, ‖A i j - B i j‖ ≤ δ) :
    ‖A.det - B.det‖ ≤ k.factorial * (k * C ^ k * δ) := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hsign : ∀ σ : Equiv.Perm (Fin k), ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := fun σ => by
    rw [Complex.norm_intCast]
    norm_num [← Int.cast_abs, Equiv.Perm.sign_abs]
  calc ∑ σ : Equiv.Perm (Fin k), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i -
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B (σ i) i‖
      ≤ ∑ _σ : Equiv.Perm (Fin k), (k * C ^ k * δ) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [← mul_sub, norm_mul, hsign, one_mul]
        have := norm_prod_sub_prod_le_of_le Finset.univ (fun i => A (σ i) i) (fun i => B (σ i) i)
          hC hδ (fun i _ => hA _ _) (fun i _ => hB _ _) (fun i _ => hAB _ _)
        simpa using this
    _ = k.factorial * (k * C ^ k * δ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- A determinant with entries bounded by `C ≥ 0` is at most `k! C^k`. -/
theorem norm_det_le {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) {C : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ C) : ‖A.det‖ ≤ k.factorial * C ^ k := by
  classical
  rw [Matrix.det_apply']
  refine (norm_sum_le _ _).trans ?_
  calc ∑ σ : Equiv.Perm (Fin k), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖
      ≤ ∑ _σ : Equiv.Perm (Fin k), C ^ k := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [norm_mul, Complex.norm_intCast, norm_prod]
        have hs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
          norm_num [← Int.cast_abs, Equiv.Perm.sign_abs]
        rw [hs, one_mul]
        exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => hA _ _).trans_eq
          (by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin])
    _ = k.factorial * C ^ k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-! ### The Hankel determinant of the image -/

/-- Rescaling a Hankel matrix by `r`: `det(x_{i+j}) = (Π_i r^i)² det(x_{i+j}/r^{i+j})`. -/
theorem det_hankel_scale {k : ℕ} {r : ℂ} (hr : r ≠ 0) (x : ℕ → ℂ) :
    (Matrix.of fun i j : Fin k => x (i + j)).det =
      (∏ i : Fin k, r ^ (i : ℕ)) ^ 2 *
        (Matrix.of fun i j : Fin k => x (i + j) / r ^ ((i : ℕ) + (j : ℕ))).det := by
  have e : (Matrix.of fun i j : Fin k => x (i + j)) =
      Matrix.of fun i j : Fin k => r ^ (i : ℕ) * (r ^ (j : ℕ) *
        (x (i + j) / r ^ ((i : ℕ) + (j : ℕ)))) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [pow_add]
    field_simp
  rw [e]
  have h1 := Matrix.det_mul_column (fun i : Fin k => r ^ (i : ℕ))
    (Matrix.of fun i j : Fin k => r ^ (j : ℕ) * (x (i + j) / r ^ ((i : ℕ) + (j : ℕ))))
  have h2 := Matrix.det_mul_row (fun j : Fin k => r ^ (j : ℕ))
    (Matrix.of fun i j : Fin k => x (i + j) / r ^ ((i : ℕ) + (j : ℕ)))
  simp only [Matrix.of_apply] at h1 h2
  rw [h1, h2, sq, mul_assoc]

/-- The image discriminant of order `k` of a sequence of window images `W_j`. -/
def imageDiscriminant (k : ℕ) (W : ℕ → ℂ) : ℂ :=
  ((k : ℂ) / W 0) ^ k * (∏ i : Fin k, ((-I) ^ (i : ℕ))⁻¹) ^ 2 *
    (Matrix.of fun i j : Fin k => W (i + j)).det

/-- **The normalization cancels.** For `m_j = W_j/((−i)^j Φ)`,
`imageDiscriminant k W = (k/m₀)^k det(m_{i+j})`. -/
theorem imageDiscriminant_eq {k : ℕ} {W : ℕ → ℂ} {Φ : ℂ} (hΦ : Φ ≠ 0) :
    imageDiscriminant k W = ((k : ℂ) / (W 0 / ((-I) ^ 0 * Φ))) ^ k *
      (Matrix.of fun i j : Fin k => W (i + j) / ((-I) ^ (i + j : ℕ) * Φ)).det := by
  have hI : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have e : (Matrix.of fun i j : Fin k => W (i + j) / ((-I) ^ (i + j : ℕ) * Φ)) =
      Matrix.of fun i j : Fin k => ((-I) ^ (i : ℕ))⁻¹ * (((-I) ^ (j : ℕ))⁻¹ *
        (Φ⁻¹ * W (i + j))) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [pow_add]
    field_simp
  rw [e]
  have h1 := Matrix.det_mul_column (fun i : Fin k => ((-I) ^ (i : ℕ))⁻¹)
    (Matrix.of fun i j : Fin k => ((-I) ^ (j : ℕ))⁻¹ * (Φ⁻¹ * W (i + j)))
  have h2 := Matrix.det_mul_row (fun j : Fin k => ((-I) ^ (j : ℕ))⁻¹)
    (Matrix.of fun i j : Fin k => Φ⁻¹ * W (i + j))
  have h3 : (Matrix.of fun i j : Fin k => Φ⁻¹ * W (i + j)) =
      Φ⁻¹ • Matrix.of fun i j : Fin k => W (i + j) := by
    ext i j; simp
  simp only [Matrix.of_apply] at h1 h2
  rw [h1, h2, h3, Matrix.det_smul, Fintype.card_fin, imageDiscriminant, pow_zero, one_mul]
  rw [div_div_eq_mul_div]
  have hΦk : Φ ^ k * Φ⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hΦ, one_pow]
  linear_combination (-(((k : ℂ) / W 0) ^ k * (∏ i : Fin k, ((-I) ^ (i : ℕ))⁻¹) ^ 2 *
    (Matrix.of fun i j : Fin k => W (i + j)).det)) * hΦk

/-! ### The discriminant of a cluster, uniformly in the height -/

/-- The error of the cluster readout at radius `r`, polynomial rate `P` and tail `E`:
with `δ = krP + E/r^{2k−2}`, `C = k + δ`, `S = (Π_{i<k} r^i)² k!` and `q = 2^{k+1}(krP + E)`,
`q (S C^k + S·kC^kδ) + S·kC^kδ`. -/
def clusterReadError (k : ℕ) (r P E : ℝ) : ℝ :=
  2 ^ (k + 1) * (k * r * P + E) *
      ((∏ i : Fin k, r ^ (i : ℕ)) ^ 2 * k.factorial * (k + (k * r * P + E / r ^ (2 * k - 2))) ^ k +
        (∏ i : Fin k, r ^ (i : ℕ)) ^ 2 * k.factorial *
          (k * (k + (k * r * P + E / r ^ (2 * k - 2))) ^ k * (k * r * P + E / r ^ (2 * k - 2)))) +
    (∏ i : Fin k, r ^ (i : ℕ)) ^ 2 * k.factorial *
      (k * (k + (k * r * P + E / r ^ (2 * k - 2))) ^ k * (k * r * P + E / r ^ (2 * k - 2)))

theorem sum_cluster_points {k : ℕ} (p : Fin k → ℂ) (f : ℂ → ℂ) :
    ∑ z ∈ Finset.univ.image p, (∑ i, (if z = p i then 1 else 0) : ℂ) * f z = ∑ i, f (p i) := by
  classical
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq' (Finset.univ.image p) (p i) f, if_pos (Finset.mem_image_of_mem p
    (Finset.mem_univ i))]

theorem sum_norm_cluster_points_le {k : ℕ} (p : Fin k → ℂ) :
    ∑ z ∈ Finset.univ.image p, ‖(∑ i, (if z = p i then 1 else 0) : ℂ)‖ ≤ k := by
  classical
  have h : ∀ z, ‖(∑ i, (if z = p i then 1 else 0) : ℂ)‖ ≤ ∑ i, (if z = p i then 1 else 0 : ℝ) :=
    fun z => (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => by
      split_ifs <;> simp))
  refine (Finset.sum_le_sum fun z _ => h z).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq' (Finset.univ.image p), Finset.mem_image_of_mem p
    (Finset.mem_univ _), if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-- **The moment-to-discriminant step.** If the approximate moments satisfy
`‖m_l − Σ_i a_i^l‖ ≤ k r^{l+1} P + E` for `l ≤ 2k − 2`, with `‖a_i‖ ≤ r ≤ 1` and `krP + E ≤ k/2`,
then `‖(k/m₀)^k det(m_{i+j}) − Π_{i<j}(a_j − a_i)²‖ ≤ clusterReadError k r P E`. -/
theorem cluster_disc_of_moments {k : ℕ} (hk : 1 ≤ k) {a : Fin k → ℂ} {m : ℕ → ℂ} {r P E : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hδ₀k : k * r * P + E ≤ k / 2)
    (ha : ∀ i, ‖a i‖ ≤ r)
    (hread' : ∀ l, l ≤ 2 * k - 2 → ‖m l - ∑ i, a i ^ l‖ ≤ k * r ^ (l + 1) * P + E) :
    ‖((k : ℂ) / m 0) ^ k * (Matrix.of fun i j : Fin k => m (i + j)).det -
        (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) ^ 2‖ ≤ clusterReadError k r P E := by
  classical
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hμ : ∀ l, ‖∑ i, a i ^ l‖ ≤ k * r ^ l := by
    intro l
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i, ‖a i ^ l‖ ≤ r ^ l := fun i => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (ha i) l
    refine (Finset.sum_le_sum fun i _ => this i).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the normalized Hankel matrices
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = k * r * P + E / r ^ (2 * k - 2) := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hentry : ∀ i j : Fin k,
      ‖(∑ l, a l ^ ((i : ℕ) + (j : ℕ))) / (r : ℂ) ^ ((i : ℕ) + (j : ℕ)) -
        m (i + j) / (r : ℂ) ^ ((i : ℕ) + (j : ℕ))‖ ≤ δ := by
    intro i j
    have hl : (i : ℕ) + (j : ℕ) ≤ 2 * k - 2 := by omega
    rw [← sub_div, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_le_iff₀ (pow_pos hr0 _), norm_sub_rev]
    have h1 := hread' _ hl
    have h2 : E ≤ E / r ^ (2 * k - 2) * r ^ ((i : ℕ) + (j : ℕ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr0 _)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1 hl) hE0
    have e1 : (k : ℝ) * r ^ ((i : ℕ) + (j : ℕ) + 1) * P =
        k * r * P * r ^ ((i : ℕ) + (j : ℕ)) := by ring
    have e2 : δ * r ^ ((i : ℕ) + (j : ℕ)) = k * r * P * r ^ ((i : ℕ) + (j : ℕ)) +
        E / r ^ (2 * k - 2) * r ^ ((i : ℕ) + (j : ℕ)) := by rw [hδ]; ring
    rw [e2]
    linarith [h1, h2, e1]
  have hA : ∀ i j : Fin k, ‖(∑ l, a l ^ ((i : ℕ) + (j : ℕ))) / (r : ℂ) ^ ((i : ℕ) + (j : ℕ))‖ ≤
      k + δ := by
    intro i j
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_le_iff₀ (pow_pos hr0 _)]
    have h1 := hμ ((i : ℕ) + (j : ℕ))
    have h2 := mul_nonneg hδ0 (pow_pos hr0 ((i : ℕ) + (j : ℕ))).le
    have e : (k + δ) * r ^ ((i : ℕ) + (j : ℕ)) =
        k * r ^ ((i : ℕ) + (j : ℕ)) + δ * r ^ ((i : ℕ) + (j : ℕ)) := by ring
    linarith
  have hB : ∀ i j : Fin k, ‖m (i + j) / (r : ℂ) ^ ((i : ℕ) + (j : ℕ))‖ ≤ k + δ := by
    intro i j
    have h1 := hentry i j
    have h2 : ‖(∑ l, a l ^ ((i : ℕ) + (j : ℕ))) / (r : ℂ) ^ ((i : ℕ) + (j : ℕ))‖ ≤ k := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
        div_le_iff₀ (pow_pos hr0 _)]
      exact hμ _
    have := norm_sub_norm_le (m (i + j) / (r : ℂ) ^ ((i : ℕ) + (j : ℕ)))
      ((∑ l, a l ^ ((i : ℕ) + (j : ℕ))) / (r : ℂ) ^ ((i : ℕ) + (j : ℕ)))
    rw [norm_sub_rev] at this
    linarith
  have hdet := norm_det_sub_le _ _ (by linarith : (1 : ℝ) ≤ k + δ) hδ0 hA hB hentry
  have hdetA := norm_det_le (Matrix.of fun i j : Fin k =>
    (∑ l, a l ^ ((i : ℕ) + (j : ℕ))) / (r : ℂ) ^ ((i : ℕ) + (j : ℕ))) hA
  -- unscaled
  have hscaleμ := det_hankel_scale (k := k) hrC (fun l => ∑ i, a i ^ l)
  have hscalem := det_hankel_scale (k := k) hrC m
  have hdisc : (Matrix.of fun i j : Fin k => ∑ l, a l ^ ((i : ℕ) + (j : ℕ))).det =
      (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) ^ 2 := by
    rw [HTGeometry.det_powerSum_hankel a]
  obtain ⟨Sr, hSr⟩ : ∃ Sr, Sr = (∏ i : Fin k, r ^ (i : ℕ)) ^ 2 := ⟨_, rfl⟩
  have hSr0 : 0 ≤ Sr := by rw [hSr]; positivity
  have hnormS : ‖(∏ i : Fin k, (r : ℂ) ^ (i : ℕ)) ^ 2‖ = Sr := by
    rw [hSr, norm_pow, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hHm : (Matrix.of fun i j : Fin k => m (i + j)).det -
      (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) ^ 2 =
        (∏ i : Fin k, (r : ℂ) ^ (i : ℕ)) ^ 2 *
          ((Matrix.of fun i j : Fin k => m (i + j) / (r : ℂ) ^ ((i : ℕ) + (j : ℕ))).det -
            (Matrix.of fun i j : Fin k =>
              (∑ l, a l ^ ((i : ℕ) + (j : ℕ))) / (r : ℂ) ^ ((i : ℕ) + (j : ℕ))).det) := by
    rw [← hdisc, hscalem, hscaleμ]; ring
  obtain ⟨errH, herrH⟩ : ∃ errH, errH = Sr * (k.factorial * (k * (k + δ) ^ k * δ)) := ⟨_, rfl⟩
  have hHm' : ‖(Matrix.of fun i j : Fin k => m (i + j)).det -
      (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) ^ 2‖ ≤ errH := by
    rw [hHm, norm_mul, hnormS, norm_sub_rev, herrH]
    exact mul_le_mul_of_nonneg_left hdet hSr0
  have hDisc : ‖(∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) ^ 2‖ ≤
      Sr * (k.factorial * (k + δ) ^ k) := by
    rw [← hdisc, hscaleμ, norm_mul, hnormS]
    exact mul_le_mul_of_nonneg_left hdetA hSr0
  -- the normalization `(k/m₀)^k`
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, δ₀ = k * r * P + E := ⟨_, rfl⟩
  have hδ₀0 : 0 ≤ δ₀ := by rw [hδ₀]; positivity
  have hm0 : ‖m 0 - k‖ ≤ δ₀ := by
    have := hread' 0 (Nat.zero_le _)
    simp only [pow_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, zero_add, pow_one] at this
    rw [hδ₀]; exact this
  have hδ₀k' : δ₀ ≤ k / 2 := by rw [hδ₀]; exact hδ₀k
  have hm0n : (k : ℝ) / 2 ≤ ‖m 0‖ := by
    have := norm_sub_norm_le (k : ℂ) (m 0)
    rw [Complex.norm_natCast, norm_sub_rev] at this
    linarith
  have hm00 : m 0 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hq1 : ‖(k : ℂ) / m 0 - 1‖ ≤ 2 * δ₀ / k := by
    rw [div_sub_one hm00, norm_div, norm_sub_rev, div_le_div_iff₀ (by linarith) (by linarith)]
    have h1 := mul_le_mul_of_nonneg_right hm0 (by linarith : (0 : ℝ) ≤ k)
    have h2 := mul_le_mul_of_nonneg_left hm0n (by linarith : (0 : ℝ) ≤ 2 * δ₀)
    linarith
  have hq2 : ‖(k : ℂ) / m 0‖ ≤ 2 := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]; linarith
  have hq : ‖((k : ℂ) / m 0) ^ k - 1‖ ≤ 2 ^ (k + 1) * δ₀ := by
    have h := norm_prod_sub_prod_le_of_le (Finset.univ : Finset (Fin k)) (fun _ => (k : ℂ) / m 0)
      (fun _ => 1) (by norm_num : (1 : ℝ) ≤ 2) (div_nonneg (by linarith) (by linarith))
      (fun _ _ => hq2)
      (fun _ _ => by simp) (fun _ _ => hq1)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow] at h
    refine h.trans (le_of_eq ?_)
    field_simp
    ring
  -- assembling
  have e : ((k : ℂ) / m 0) ^ k * (Matrix.of fun i j : Fin k => m (i + j)).det -
      (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) ^ 2 =
        (((k : ℂ) / m 0) ^ k - 1) * (Matrix.of fun i j : Fin k => m (i + j)).det +
          ((Matrix.of fun i j : Fin k => m (i + j)).det -
            (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) ^ 2) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hdetm : ‖(Matrix.of fun i j : Fin k => m (i + j)).det‖ ≤
      Sr * (k.factorial * (k + δ) ^ k) + errH := by
    have := norm_sub_norm_le (Matrix.of fun i j : Fin k => m (i + j)).det
      ((∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) ^ 2)
    linarith
  have hfin := add_le_add (mul_le_mul hq hdetm (norm_nonneg _)
    (mul_nonneg (by positivity) hδ₀0)) hHm'
  refine hfin.trans (le_of_eq ?_)
  rw [herrH, hSr, hδ₀, hδ, clusterReadError]
  ring

/-- **The image reads the discriminant of a cluster, uniformly in the height.** Let `k ≥ 1`,
`0 ≤ θ`, `λ > θ/2`, `A, S, M' ≥ 0`, `K' ≥ 3`. For all `T ≥ T₀`: let `Z` be tempered with
`Σ m(z)/(1 + |γ_z|²) ≤ S` and local count `≤ (θ/2π) log(T/2π)(y − x) + A log(T/2π)` in
`[T/2, 3T/2]`. Let the points of `Z` in the disc `‖z − z₀‖ ≤ r`, `0 < r ≤ T^{−(M' + κ_λ + 1)}`, be
`p₀, …, p_{k−1}` (with multiplicity), every other point in `[T/2, 3T/2]` at distance `≥ T^{−M'}`.
Then windows of aperture `λ · ½ log(T/2π)` have images `W_j`, `j ≤ 2k − 2`, with
`‖imageDiscriminant k W − Π_{i<j}(γ_{p_j} − γ_{p_i})²‖ ≤ clusterReadError k r T^{M' + κ_λ} E`,
`E = e^{−K' log³(T/2π)}`. -/
theorem cluster_discriminant_rvm (k : ℕ) (hk : 1 ≤ k) {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 3 ≤ K') :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z : ZeroConfig, TemperedConfig Z →
        ∑' z, ‖multDiff Z emptyZeroConfig z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z emptyZeroConfig z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 < r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z emptyZeroConfig z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ p : Fin k → ℂ, (∀ i, ‖p i - z₀‖ ≤ r) →
        (∀ z, ‖z - z₀‖ ≤ r → multDiff Z emptyZeroConfig z = ∑ i, (if z = p i then 1 else 0)) →
        ∃ (F : ℕ → ℝ → ℂ) (G : ℝ → ℂ),
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
          (∀ j, j ≤ 2 * k - 2 → ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) (F j)) ∧
          ‖imageDiscriminant k (fun j => Z.W (F j) G) -
              (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (gammaOf (p j) - gammaOf (p i))) ^ 2‖ ≤
            clusterReadError k r (T ^ (M' + slowExponent lam))
              (Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3))) := by
  classical
  obtain ⟨T₀, hT₀, hread⟩ := discMoment_readout_rvm (2 * k - 2) hθ hlam hA hS hM'
    (by linarith : 0 ≤ K')
  refine ⟨T₀, hT₀, fun T hT Z hZ hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso p hp hc => ?_⟩
  set s : Finset ℂ := Finset.univ.image p with hs
  have hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact hp i
  have hds : ∀ z, multDiff Z emptyZeroConfig z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s := by
    intro z hcz hzr
    by_contra hzs
    apply hcz
    rw [hc z hzr]
    refine Finset.sum_eq_zero fun i _ => if_neg fun h => hzs ?_
    rw [h]; exact Finset.mem_image_of_mem p (Finset.mem_univ i)
  obtain ⟨F₁, G₁, -, hG₁, hΦ, hj⟩ := hread T hT Z emptyZeroConfig hZ temperedConfig_emptyZeroConfig
    hStail hcount z₀ hz₀ hz₀re r hr0.le hr hiso s hsd hds
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = T ^ (M' + slowExponent lam) := ⟨_, rfl⟩
  rw [← hE, ← hP] at hj ⊢
  set ω := gammaOf z₀
  set Φ := pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀ with hΦdef
  set W : ℕ → ℂ := fun j => Z.W (localWindow z₀.im (annihilatePow (ω - z₀.im) j F₁))
    (localWindow z₀.im G₁) with hW
  set m : ℕ → ℂ := fun j => W j / ((-I) ^ j * Φ) with hm
  set a : Fin k → ℂ := fun i => gammaOf (p i) - ω with ha
  -- the scales
  have h2πe : 4 ≤ 2 * π * Real.exp 1 := by
    have h1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [Real.pi_gt_three]
  have hT4 : 4 ≤ T := h2πe.trans (hT₀.trans hT)
  have hT0 : 0 < T := by linarith
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg hT0.le _
  have hrP : r * P ≤ 1 / 4 := by
    have hprod : T ^ (-(M' + slowExponent lam + 1)) * P = T⁻¹ := by
      rw [hP, ← Real.rpow_add hT0, show -(M' + slowExponent lam + 1) + (M' + slowExponent lam) =
        -1 by ring, Real.rpow_neg_one]
    have h1 : r * P ≤ T⁻¹ := hprod ▸ mul_le_mul_of_nonneg_right hr hP0
    have h2 : T⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ hT0 (by norm_num), one_div, inv_inv]; exact hT4
    linarith
  have hr1 : r ≤ 1 := by
    have hT1 : 1 ≤ T := by linarith
    have hx : 1 ≤ M' + slowExponent lam := by
      unfold slowExponent; have := mul_pos Real.pi_pos (show 0 < lam by linarith); linarith
    have h := hr.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith : -(M' + slowExponent lam
      + 1) ≤ (-1 : ℝ)))
    rw [Real.rpow_neg_one] at h
    exact h.trans (inv_le_one_of_one_le₀ hT1)
  have hu1 : 1 ≤ Real.log (T / (2 * π)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    linarith [hT₀, hT]
  have hE4 : E ≤ 1 / 4 := by
    rw [hE, Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    have h3 : 3 ≤ K' * Real.log (T / (2 * π)) ^ 3 := by
      have : 1 ≤ Real.log (T / (2 * π)) ^ 3 := one_le_pow₀ hu1
      nlinarith
    linarith [Real.add_one_le_exp (K' * Real.log (T / (2 * π)) ^ 3)]
  have hE0 : 0 ≤ E := by rw [hE]; exact (Real.exp_pos _).le
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- the moments of the cluster
  have hsum : ∀ f : ℂ → ℂ, ∑ z ∈ s, multDiff Z emptyZeroConfig z * f z = ∑ i, f (p i) := by
    intro f
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)], sum_cluster_points]
  have hN : ∑ z ∈ s, ‖multDiff Z emptyZeroConfig z‖ ≤ k := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)]]
    exact sum_norm_cluster_points_le p
  have hread' : ∀ l, l ≤ 2 * k - 2 → ‖m l - ∑ i, a i ^ l‖ ≤ k * r ^ (l + 1) * P + E := by
    intro l hl
    obtain ⟨-, hb⟩ := hj l hl
    rw [W_emptyZeroConfig, sub_zero, hsum] at hb
    refine hb.trans ?_
    have := mul_le_mul_of_nonneg_right hN (mul_nonneg (pow_nonneg hr0.le (l + 1)) hP0)
    linarith
  -- assembling
  have hδ₀k : k * r * P + E ≤ k / 2 := by
    have := mul_le_mul_of_nonneg_left hrP (by linarith : (0 : ℝ) ≤ k)
    have e : (k : ℝ) * r * P = k * (r * P) := by ring
    linarith
  have hal : ∀ i, ‖a i‖ ≤ r := fun i => by
    rw [ha]; simp only; rw [norm_gammaOf_sub]; exact hp i
  have hmain := cluster_disc_of_moments hk hr0 hr1 hP0 hE0 hδ₀k hal hread'
  have hdisc : (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) =
      ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (gammaOf (p j) - gammaOf (p i)) :=
    Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by simp only [ha]; ring
  rw [hdisc] at hmain
  have hD := imageDiscriminant_eq (k := k) (W := W) hΦ
  refine ⟨fun j => localWindow z₀.im (annihilatePow (ω - z₀.im) j F₁), localWindow z₀.im G₁,
    apertureWindow_localWindow hG₁ _, fun j hjk => (hj j hjk).1, ?_⟩
  change ‖imageDiscriminant k W - _‖ ≤ _
  rw [hD]
  exact hmain

end GaloisForLFunctions.ZeroConfigurationGeometry
