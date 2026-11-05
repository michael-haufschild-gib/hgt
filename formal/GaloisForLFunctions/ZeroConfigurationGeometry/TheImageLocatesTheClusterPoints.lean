import GaloisForLFunctions.ZeroConfigurationGeometry.TheImageReadsTheDiscriminantOfACluster

/-!
# The image locates the points of a cluster

For a cluster `a₀, …, a_{k−1}` with power sums `μ_l = Σ_i a_i^l`, the bordered Hankel determinant

`Q(x) = det [ x^j ; μ_{i+j} ]_{i < k, j ≤ k}`

equals `Disc(a) · Π_l (a_l − x)` (`det_bordered_hankel`, Heine's formula): the matrix is
`C · V(x, a)` with `V` the Vandermonde matrix of `(x, a₀, …, a_{k−1})` and `C` block diagonal with
`det C = det V(a)`. The camera reads the power sums up to order `2k − 1`, so the polynomial `Q̃`
built from the read moments is uniformly close to `Disc(a) Π(a_l − x)` on the disc
(`bordered_of_moments`, `cluster_location_rvm`). Its zeros locate the cluster: a zero `x` of `Q̃`
lies within `(R/|Disc|)^{1/k}` of a cluster point (`exists_near_point_of_bordered_zero`).
-/

open MeasureTheory Complex Set Filter Matrix
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- The bordered Hankel matrix: first row `x^j`, then the rows `μ_{i+j}`, `j ≤ k`. -/
def borderedHankel (k : ℕ) (μ : ℕ → ℂ) (x : ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.of fun i j => Fin.cases (x ^ (j : ℕ)) (fun i' : Fin k => μ ((i' : ℕ) + (j : ℕ))) i

/-- **Heine's formula.** `det [x^j; μ_{i+j}] = Disc(a) · Π_l (a_l − x)` for the power sums of `a`. -/
theorem det_bordered_hankel {k : ℕ} (a : Fin k → ℂ) (x : ℂ) :
    (borderedHankel k (fun l => ∑ i, a i ^ l) x).det =
      (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) ^ 2 * ∏ l, (a l - x) := by
  classical
  set C : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.of fun i l =>
    Fin.cases (Fin.cases 1 (fun _ => 0) l) (fun i' : Fin k => Fin.cases 0 (fun l' : Fin k =>
      a l' ^ (i' : ℕ)) l) i with hC
  have hB : borderedHankel k (fun l => ∑ i, a i ^ l) x =
      C * Matrix.vandermonde (Fin.cons x a : Fin (k + 1) → ℂ) := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [borderedHankel, hC, Matrix.vandermonde_apply]
    · simp only [borderedHankel, hC, Matrix.of_apply, Fin.cases_succ, Fin.cases_zero, zero_mul,
        zero_add, Matrix.vandermonde_apply, Fin.cons_succ]
      exact Finset.sum_congr rfl fun l _ => by rw [pow_add]
  have hdetC : C.det = (Matrix.vandermonde a).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have h0 : ∀ j : Fin k, C 0 j.succ = 0 := fun j => by simp [hC]
    simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have hC00 : C 0 0 = 1 := by simp [hC]
    rw [hC00, mul_one, Fin.val_zero, pow_zero, one_mul]
    rw [← Matrix.det_transpose (Matrix.vandermonde a)]
    congr 1
  have hV : (Matrix.vandermonde (Fin.cons x a : Fin (k + 1) → ℂ)).det =
      (∏ l, (a l - x)) * ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i) := by
    rw [Matrix.det_vandermonde, Fin.prod_univ_succ, Fin.prod_Ioi_zero]
    congr 1
    simp
  rw [hB, Matrix.det_mul, hdetC, hV, Matrix.det_vandermonde]
  ring

/-! ### Read moments locate the cluster -/

/-- The error of the located cluster: with `δ = krP + E/r^{2k−1}` and `C = k + δ`,
`(Π_{j ≤ k} r^j)(Π_{i<k} r^i) · (k+1)! · (k+1)C^{k+1}δ`, of the scale `r^{k²}` of `Q`. -/
def borderError (k : ℕ) (r P E : ℝ) : ℝ :=
  (∏ j : Fin (k + 1), r ^ (j : ℕ)) * (∏ i : Fin k, r ^ (i : ℕ)) *
    ((k + 1).factorial * ((k + 1) * (k + (k * r * P + E / r ^ (2 * k - 1))) ^ (k + 1) *
      (k * r * P + E / r ^ (2 * k - 1))))

/-- **The polynomial of read moments.** If `‖m_l − Σ_i a_i^l‖ ≤ k r^{l+1} P + E` for
`l ≤ 2k − 1`, `‖a_i‖ ≤ r ≤ 1`, then on the disc `‖x‖ ≤ r`
`‖det [x^j; m_{i+j}] − Disc(a) Π_l (a_l − x)‖ ≤ borderError k r P E`. -/
theorem bordered_of_moments {k : ℕ} (hk : 1 ≤ k) {a : Fin k → ℂ} {m : ℕ → ℂ} {r P E : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (ha : ∀ i, ‖a i‖ ≤ r)
    (hread' : ∀ l, l ≤ 2 * k - 1 → ‖m l - ∑ i, a i ^ l‖ ≤ k * r ^ (l + 1) * P + E) {x : ℂ}
    (hx : ‖x‖ ≤ r) :
    ‖(borderedHankel k m x).det -
        (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) ^ 2 * ∏ l, (a l - x)‖ ≤
      borderError k r P E := by
  classical
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hnr : ∀ n : ℕ, ‖(r : ℂ) ^ n‖ = r ^ n := fun n => by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hμ : ∀ l, ‖∑ i, a i ^ l‖ ≤ k * r ^ l := by
    intro l
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i, ‖a i ^ l‖ ≤ r ^ l := fun i => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (ha i) l
    refine (Finset.sum_le_sum fun i _ => this i).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = k * r * P + E / r ^ (2 * k - 1) := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  -- the scaled bordered matrices
  set ρ : Fin (k + 1) → ℂ := Fin.cases 1 (fun i' : Fin k => (r : ℂ) ^ (i' : ℕ)) with hρ
  set S : (ℕ → ℂ) → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun μ => Matrix.of fun i j =>
    Fin.cases (x ^ (j : ℕ) / (r : ℂ) ^ (j : ℕ))
      (fun i' : Fin k => μ ((i' : ℕ) + (j : ℕ)) / (r : ℂ) ^ ((i' : ℕ) + (j : ℕ))) i with hS
  have hscale : ∀ μ : ℕ → ℂ, (borderedHankel k μ x).det =
      (∏ i, ρ i) * ((∏ j : Fin (k + 1), (r : ℂ) ^ (j : ℕ)) * (S μ).det) := by
    intro μ
    have e : borderedHankel k μ x = Matrix.of fun i j : Fin (k + 1) =>
        ρ i * ((r : ℂ) ^ (j : ℕ) * S μ i j) := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp only [borderedHankel, hρ, hS, Matrix.of_apply, Fin.cases_zero, one_mul]
        field_simp
      · simp only [borderedHankel, hρ, hS, Matrix.of_apply, Fin.cases_succ]
        rw [pow_add]
        field_simp
    rw [e]
    have h1 := Matrix.det_mul_column ρ (Matrix.of fun i j : Fin (k + 1) =>
      (r : ℂ) ^ (j : ℕ) * S μ i j)
    have h2 := Matrix.det_mul_row (fun j : Fin (k + 1) => (r : ℂ) ^ (j : ℕ)) (S μ)
    simp only [Matrix.of_apply] at h1 h2
    rw [h1, h2]
  have hρn : ‖∏ i, ρ i‖ = ∏ i : Fin k, r ^ (i : ℕ) := by
    rw [norm_prod, Fin.prod_univ_succ]
    simp only [hρ, Fin.cases_zero, Fin.cases_succ, norm_one, one_mul]
    exact Finset.prod_congr rfl fun i _ => hnr _
  have hcn : ‖∏ j : Fin (k + 1), (r : ℂ) ^ (j : ℕ)‖ = ∏ j : Fin (k + 1), r ^ (j : ℕ) := by
    rw [norm_prod]; exact Finset.prod_congr rfl fun j _ => hnr _
  -- entry bounds
  have hxj : ∀ j : Fin (k + 1), ‖x ^ (j : ℕ) / (r : ℂ) ^ (j : ℕ)‖ ≤ 1 := fun j => by
    rw [norm_div, hnr, norm_pow, div_le_one (pow_pos hr0 _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx _
  set μa : ℕ → ℂ := fun l => ∑ i, a i ^ l with hμa
  have hent : ∀ (i' : Fin k) (j : Fin (k + 1)),
      ‖μa ((i' : ℕ) + (j : ℕ)) / (r : ℂ) ^ ((i' : ℕ) + (j : ℕ)) -
        m ((i' : ℕ) + (j : ℕ)) / (r : ℂ) ^ ((i' : ℕ) + (j : ℕ))‖ ≤ δ := by
    intro i' j
    have hl : (i' : ℕ) + (j : ℕ) ≤ 2 * k - 1 := by omega
    rw [← sub_div, norm_div, hnr, div_le_iff₀ (pow_pos hr0 _), norm_sub_rev]
    have h1 := hread' _ hl
    have h2 : E ≤ E / r ^ (2 * k - 1) * r ^ ((i' : ℕ) + (j : ℕ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hr0 _)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1 hl) hE0
    have e1 : (k : ℝ) * r ^ ((i' : ℕ) + (j : ℕ) + 1) * P =
        k * r * P * r ^ ((i' : ℕ) + (j : ℕ)) := by ring
    have e2 : δ * r ^ ((i' : ℕ) + (j : ℕ)) = k * r * P * r ^ ((i' : ℕ) + (j : ℕ)) +
        E / r ^ (2 * k - 1) * r ^ ((i' : ℕ) + (j : ℕ)) := by rw [hδ]; ring
    rw [e2]
    linarith [h1, h2, e1]
  have hAμ : ∀ (i' : Fin k) (j : Fin (k + 1)),
      ‖μa ((i' : ℕ) + (j : ℕ)) / (r : ℂ) ^ ((i' : ℕ) + (j : ℕ))‖ ≤ k := fun i' j => by
    rw [norm_div, hnr, div_le_iff₀ (pow_pos hr0 _)]; exact hμ _
  have hC1 : (1 : ℝ) ≤ k + δ := by linarith
  have hSA : ∀ i j, ‖S μa i j‖ ≤ k + δ := by
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [hS, Matrix.of_apply, Fin.cases_zero]; exact (hxj j).trans hC1
    · simp only [hS, Matrix.of_apply, Fin.cases_succ]; linarith [hAμ i' j]
  have hSB : ∀ i j, ‖S m i j‖ ≤ k + δ := by
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [hS, Matrix.of_apply, Fin.cases_zero]; exact (hxj j).trans hC1
    · simp only [hS, Matrix.of_apply, Fin.cases_succ]
      have h1 := hent i' j
      have h2 := hAμ i' j
      have := norm_sub_norm_le (m ((i' : ℕ) + (j : ℕ)) / (r : ℂ) ^ ((i' : ℕ) + (j : ℕ)))
        (μa ((i' : ℕ) + (j : ℕ)) / (r : ℂ) ^ ((i' : ℕ) + (j : ℕ)))
      rw [norm_sub_rev (m _ / _)] at this
      linarith
  have hSd : ∀ i j, ‖S μa i j - S m i j‖ ≤ δ := by
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [hS, Matrix.of_apply, Fin.cases_zero, sub_self, norm_zero]; exact hδ0
    · simp only [hS, Matrix.of_apply, Fin.cases_succ]; exact hent i' j
  have hdet := norm_det_sub_le (S μa) (S m) hC1 hδ0 hSA hSB hSd
  -- assembling
  rw [← det_bordered_hankel a x]
  change ‖(borderedHankel k m x).det - (borderedHankel k μa x).det‖ ≤ _
  rw [hscale m, hscale μa, ← mul_sub, ← mul_sub, norm_mul, norm_mul, hρn, hcn, norm_sub_rev]
  have hP1 : 0 ≤ ∏ i : Fin k, r ^ (i : ℕ) := by positivity
  have hP2 : 0 ≤ ∏ j : Fin (k + 1), r ^ (j : ℕ) := by positivity
  calc (∏ i : Fin k, r ^ (i : ℕ)) * ((∏ j : Fin (k + 1), r ^ (j : ℕ)) * ‖(S μa).det - (S m).det‖)
      ≤ (∏ i : Fin k, r ^ (i : ℕ)) * ((∏ j : Fin (k + 1), r ^ (j : ℕ)) *
          ((k + 1).factorial * ((k + 1) * (k + δ) ^ (k + 1) * δ))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hP2) hP1
        simpa using hdet
    _ = borderError k r P E := by rw [borderError, hδ]; ring

/-- **Zeros of the read polynomial lie near the cluster.** If `‖Q − D Π_l (a_l − x)‖ ≤ R` with
`D ≠ 0` and `Q = 0`, some cluster point satisfies `‖a_l − x‖^k ≤ R/‖D‖`. -/
theorem exists_near_point_of_bordered_zero {k : ℕ} (hk : 1 ≤ k) {a : Fin k → ℂ} {D Q x : ℂ}
    {R : ℝ} (hD : D ≠ 0) (h : ‖Q - D * ∏ l, (a l - x)‖ ≤ R) (hQ : Q = 0) :
    ∃ l, ‖a l - x‖ ^ k ≤ R / ‖D‖ := by
  classical
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_min_image Finset.univ (fun l => ‖a l - x‖) hne
  refine ⟨l₀, ?_⟩
  rw [hQ, zero_sub, norm_neg, norm_mul, norm_prod] at h
  have hD0 : 0 < ‖D‖ := norm_pos_iff.mpr hD
  rw [le_div_iff₀ hD0, mul_comm]
  have hmin : ‖a l₀ - x‖ ^ k ≤ ∏ l, ‖a l - x‖ := by
    have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ => ‖a l₀ - x‖)
      (g := fun l => ‖a l - x‖) (fun _ _ => norm_nonneg _) (fun l _ => hl₀ l (Finset.mem_univ l))
    simpa [Finset.prod_const] using this
  nlinarith [mul_le_mul_of_nonneg_left hmin hD0.le]

/-! ### Uniformly in the height -/

/-- **The image locates the points of a cluster, uniformly in the height.** Let `k ≥ 1`,
`0 ≤ θ`, `λ > θ/2`, `A, S, M', K' ≥ 0`. For all `T ≥ T₀`, let `Z` be tempered with local counts of
Riemann–von Mangoldt type. Let `p₀, …, p_{k−1}` be its points (with multiplicity) in the disc
`‖z − z₀‖ ≤ r`, `0 < r ≤ T^{−(M' + κ_λ + 1)}`, every other point in `[T/2, 3T/2]` at distance
`≥ T^{−M'}`. Then windows of aperture `λ · ½ log(T/2π)` with nonzero target image `Φ` have images
`W_l`, `l ≤ 2k − 1`, such that `m_l = W_l/((−i)^l Φ)` satisfies, on the disc `‖x‖ ≤ r`,
`‖det [x^j; m_{i+j}] − Disc · Π_l (γ_{p_l} − γ_{z₀} − x)‖ ≤ borderError k r T^{M' + κ_λ} E`. -/
theorem cluster_location_rvm (k : ℕ) (hk : 1 ≤ k) {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
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
        ∃ (F : ℕ → ℝ → ℂ) (G : ℝ → ℂ) (Φ : ℂ), Φ ≠ 0 ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
          (∀ l, l ≤ 2 * k - 1 → ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) (F l)) ∧
          ∀ x : ℂ, ‖x‖ ≤ r →
            ‖(borderedHankel k (fun l => Z.W (F l) G / ((-I) ^ l * Φ)) x).det -
                (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (gammaOf (p j) - gammaOf (p i))) ^ 2 *
                  ∏ l, (gammaOf (p l) - gammaOf z₀ - x)‖ ≤
              borderError k r (T ^ (M' + slowExponent lam))
                (Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3))) := by
  classical
  obtain ⟨T₀, hT₀, hread⟩ := discMoment_readout_rvm (2 * k - 1) hθ hlam hA hS hM' hK'
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
  set a : Fin k → ℂ := fun i => gammaOf (p i) - ω with ha
  have h2πe : 4 ≤ 2 * π * Real.exp 1 := by
    have h1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [Real.pi_gt_three]
  have hT4 : 4 ≤ T := h2πe.trans (hT₀.trans hT)
  have hT0 : 0 < T := by linarith
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg hT0.le _
  have hE0 : 0 ≤ E := by rw [hE]; exact (Real.exp_pos _).le
  have hr1 : r ≤ 1 := by
    have hT1 : 1 ≤ T := by linarith
    have h := hr.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by
      unfold slowExponent; have := mul_pos Real.pi_pos (show 0 < lam by linarith); linarith :
        -(M' + slowExponent lam + 1) ≤ (-1 : ℝ)))
    rw [Real.rpow_neg_one] at h
    exact h.trans (inv_le_one_of_one_le₀ hT1)
  have hsum : ∀ f : ℂ → ℂ, ∑ z ∈ s, multDiff Z emptyZeroConfig z * f z = ∑ i, f (p i) := by
    intro f
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)], sum_cluster_points]
  have hN : ∑ z ∈ s, ‖multDiff Z emptyZeroConfig z‖ ≤ k := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)]]
    exact sum_norm_cluster_points_le p
  have hread' : ∀ l, l ≤ 2 * k - 1 →
      ‖Z.W (localWindow z₀.im (annihilatePow (ω - z₀.im) l F₁)) (localWindow z₀.im G₁) /
          ((-I) ^ l * Φ) - ∑ i, a i ^ l‖ ≤ k * r ^ (l + 1) * P + E := by
    intro l hl
    obtain ⟨-, hb⟩ := hj l hl
    rw [W_emptyZeroConfig, sub_zero, hsum] at hb
    refine hb.trans ?_
    have := mul_le_mul_of_nonneg_right hN (mul_nonneg (pow_nonneg hr0.le (l + 1)) hP0)
    linarith
  have hal : ∀ i, ‖a i‖ ≤ r := fun i => by
    rw [ha]; simp only; rw [norm_gammaOf_sub]; exact hp i
  have hdisc : (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) =
      ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (gammaOf (p j) - gammaOf (p i)) :=
    Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by simp only [ha]; ring
  refine ⟨fun l => localWindow z₀.im (annihilatePow (ω - z₀.im) l F₁), localWindow z₀.im G₁, Φ,
    hΦ, apertureWindow_localWindow hG₁ _, fun l hl => (hj l hl).1, fun x hx => ?_⟩
  have h := bordered_of_moments hk hr0 hr1 hP0 hE0 hal hread' hx
  rw [hdisc] at h
  exact h

end GaloisForLFunctions.ZeroConfigurationGeometry
