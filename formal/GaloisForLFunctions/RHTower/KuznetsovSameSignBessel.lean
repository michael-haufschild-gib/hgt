import GaloisForLFunctions.RHTower.KuznetsovSameSignGaussIdentity
import GaloisForLFunctions.RHTower.KuznetsovUniformBounds
import GaloisForLFunctions.RHTower.KuznetsovOppositeSign

/-!
# Bessel's inequality for finite combinations of Poincaré series on a line

For finitely many frequencies `μ_k > 0`, cusp vectors `ρ(T)v_k = e(μ_k)v_k` and coefficients `b_k`, let

`F_t = Σ_k b_k (2πμ_k)^{−it} U(·| σ−it, μ_k, v_k)`   (`σ > 1`).

The phases `(2πμ_k)^{−it}` cancel the factors `(ν/μ)^{it}` of the line pairings, so

`‖F_t‖² = Σ_{k,l} b̄_k b_l (2 diag_{kl} + 2 R_{kl}(t))`

(`norm_famL2_sq`), and Bessel's inequality for the cuspidal eigenbasis gives

`4 Σ_j |W(σ+it, ν_j)|² |A_j(σ)|² ≤ ‖F_t‖²`,   `A_j(σ) = Σ_k b̄_k ρ_j(v_k) (2πμ_k)^{½−σ}`

(`tsum_norm_whittMellin_sq_mul_le`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex Filter Topology
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry KuznetsovGauss

noncomputable section

variable {N : ℕ} {ι : Type*}

/-! ## Continuity of `W` on vertical lines -/

theorem ne_neg_nat_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) (m : ℕ) : s ≠ -(m : ℂ) := by
  intro hs; apply h; rw [hs]; simp

theorem ne_neg_nat_of_re_pos {s : ℂ} (h : 0 < s.re) (m : ℕ) : s ≠ -(m : ℂ) := by
  intro hs; rw [hs] at h; simp at h; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem continuousAt_whittMellin {b ν : ℂ} (h1 : ∀ m : ℕ, b - 1 / 2 ≠ -(m : ℂ))
    (h2 : ∀ m : ℕ, b - 1 / 2 + ν ≠ -(m : ℂ)) (h3 : ∀ m : ℕ, b - 1 / 2 - ν ≠ -(m : ℂ))
    (h4 : ∀ m : ℕ, 2 * (b - 1 / 2) ≠ -(m : ℂ)) :
    ContinuousAt (fun b => whittMellin b ν) b := by
  unfold whittMellin
  have hG : ∀ (f : ℂ → ℂ) (s : ℂ), (∀ m : ℕ, f s ≠ -(m : ℂ)) → ContinuousAt f s →
      ContinuousAt (fun b => Complex.Gamma (f b)) s := fun f s hs hf =>
    (Complex.differentiableAt_Gamma _ hs).continuousAt.comp hf
  refine ContinuousAt.div (ContinuousAt.mul (ContinuousAt.mul (ContinuousAt.mul ?_
    (hG (fun b => b - 1 / 2) b h1 (by fun_prop)))
    (hG (fun b => b - 1 / 2 + ν) b h2 (by fun_prop)))
    (hG (fun b => b - 1 / 2 - ν) b h3 (by fun_prop)))
    (hG (fun b => 2 * (b - 1 / 2)) b h4 (by fun_prop)) (Complex.Gamma_ne_zero h4)
  exact (by fun_prop : ContinuousAt (fun b : ℂ => b - 1 / 2 - 1) b).const_cpow (Or.inl two_ne_zero)

theorem specParam_cases (lam : ℝ) :
    (specParam lam).im = 0 ∧ |(specParam lam).re| ≤ 1 / 2 ∨ (specParam lam).re = 0 ∨
      lam < 0 := by
  by_cases h0 : lam < 0
  · exact Or.inr (Or.inr h0)
  replace h0 := not_lt.1 h0
  unfold specParam
  split_ifs with h
  · left
    refine ⟨by simp, ?_⟩
    rw [Complex.ofReal_re, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (1 / 4 - lam) ≤ Real.sqrt ((1 / 2) ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = 1 / 2 := Real.sqrt_sq (by norm_num)
  · right; left; simp

/-- `W(σ+it, ν_j)` is continuous at every `(σ, t)` with `σ ≥ 1`, `t ≠ 0`, and for `σ > 1` also at
`t = 0`. -/
theorem continuousAt_whittMellin_specParam {lam : ℝ} (hlam : 0 ≤ lam) {σ t : ℝ} (hσ : 1 ≤ σ)
    (ht : t ≠ 0 ∨ 1 < σ) :
    ContinuousAt (fun b => whittMellin b (specParam lam)) ((σ : ℂ) + t * Complex.I) := by
  have hre : ((σ : ℂ) + t * Complex.I - 1 / 2).re = σ - 1 / 2 := by simp
  have him : ((σ : ℂ) + t * Complex.I - 1 / 2).im = t := by simp
  have key : ∀ c : ℂ, c.re = σ - 1 / 2 + (c - ((σ : ℂ) + t * Complex.I - 1 / 2)).re →
      ((c - ((σ : ℂ) + t * Complex.I - 1 / 2)).im = 0 → |(c - ((σ : ℂ) + t * Complex.I - 1 / 2)).re| ≤ 1 / 2 →
        ∀ m : ℕ, c ≠ -(m : ℂ)) := by
    intro c _ himc hrec m
    rcases ht with ht | hσ1
    · refine ne_neg_nat_of_im_ne_zero ?_ m
      have : c.im = t := by
        have h := himc; simp only [Complex.sub_im, him] at h; linarith
      rw [this]; exact ht
    · refine ne_neg_nat_of_re_pos ?_ m
      have h := abs_le.1 hrec
      simp only [Complex.sub_re, hre] at h
      linarith [h.1]
  have h1 : ∀ m : ℕ, (σ : ℂ) + t * Complex.I - 1 / 2 ≠ -(m : ℂ) := fun m =>
    ne_neg_nat_of_re_pos (by rw [hre]; linarith) m
  have h4 : ∀ m : ℕ, 2 * ((σ : ℂ) + t * Complex.I - 1 / 2) ≠ -(m : ℂ) := fun m =>
    ne_neg_nat_of_re_pos (by simp; linarith) m
  rcases specParam_cases lam with ⟨hνim, hνre⟩ | hνre | hneg
  · refine continuousAt_whittMellin h1 ?_ ?_ h4
    · exact key _ (by simp) (by simpa using hνim) (by simpa using hνre)
    · exact key _ (by simp; ring) (by simpa using hνim) (by simpa [abs_neg] using hνre)
  · refine continuousAt_whittMellin h1 (fun m => ne_neg_nat_of_re_pos ?_ m)
      (fun m => ne_neg_nat_of_re_pos ?_ m) h4
    · simp only [Complex.add_re, hre, hνre]; linarith
    · simp only [Complex.sub_re, hre, hνre]; linarith
  · exact absurd hneg (not_lt.2 hlam)

theorem measurable_whittMellin_line {lam : ℝ} (hlam : 0 ≤ lam) {σ : ℝ} (hσ : 1 ≤ σ) :
    Measurable fun t : ℝ => whittMellin ((σ : ℂ) + t * Complex.I) (specParam lam) := by
  refine measurable_of_continuousOn_compl_singleton 0 fun t ht => ?_
  refine ((continuousAt_whittMellin_specParam hlam hσ (Or.inl ht)).comp
    (f := fun t : ℝ => (σ : ℂ) + t * Complex.I) (by fun_prop)).continuousWithinAt

/-! ## The combination `F_t` -/

/-- The phase-free line pairing `2 diag + 2 R_σ(t)`. -/
def linePair (σ t μ ν : ℝ) (v w : DeckSpace N) : ℂ :=
  2 * diagPlus (σ : ℂ) σ μ ν v w + 2 * ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 *
    ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))

/-- `A_j(σ) = Σ_k b̄_k ρ_j(v_k) (2πμ_k)^{½−σ}`. -/
def specCoeff (j : CuspEigenIndex N) (σ : ℝ) (s : Finset ι) (μ : ι → ℝ) (v : ι → DeckSpace N)
    (b : ι → ℂ) : ℂ :=
  ∑ k ∈ s, conj (b k) * cuspCoeff j (μ k) (v k) *
    ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((σ : ℂ) - 1 / 2))

/-- `F_t = Σ_k b_k (2πμ_k)^{−it} U(·| σ−it, μ_k, v_k)`. -/
def famL2 {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    (v : ι → DeckSpace N) (b : ι → ℂ) : DeckL2 N :=
  ∑ k ∈ s, (b k * ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I))) •
    toDeckL2 _ (memLp_poincSeries_profile (s := (σ : ℂ) - t * Complex.I) (by simpa using hσ)
      (hμ k) (v k))

theorem conj_ofReal_cpow_neg_mul_I {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    conj (((x : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I))) = ((x : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
  rw [conj_ofReal_cpow hx]
  congr 1
  simp

theorem phase_cancel {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (t : ℝ) :
    conj (((2 * Real.pi * μ : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I))) *
      ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) *
      (((ν / μ : ℝ)) : ℂ) ^ ((t : ℂ) * Complex.I) = 1 := by
  have hπμ : (0 : ℝ) < 2 * Real.pi * μ := by positivity
  have hπν : (0 : ℝ) < 2 * Real.pi * ν := by positivity
  rw [conj_ofReal_cpow_neg_mul_I hπμ.le, show ν / μ = (2 * Real.pi * ν) / (2 * Real.pi * μ) by
    field_simp]
  have h := ofReal_cpow_mul_ofReal_div_cpow hπμ hπν.le ((t : ℂ) * Complex.I)
  have hne : ((2 * Real.pi * ν : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hπν.ne' (Complex.ofReal_eq_zero.1 h.1)
  rw [Complex.cpow_neg]
  calc ((2 * Real.pi * μ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) *
        (((2 * Real.pi * ν : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ *
        (((2 * Real.pi * ν / (2 * Real.pi * μ) : ℝ)) : ℂ) ^ ((t : ℂ) * Complex.I)
      = (((2 * Real.pi * μ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) *
        (((2 * Real.pi * ν / (2 * Real.pi * μ) : ℝ)) : ℂ) ^ ((t : ℂ) * Complex.I)) *
        (((2 * Real.pi * ν : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ := by ring
    _ = 1 := by rw [h, mul_inv_cancel₀ hne]

theorem phase_mul_diagPlus {μ ν : ℝ} (hμ : 0 < μ) (σ t : ℝ) (v w : DeckSpace N) :
    conj (((2 * Real.pi * μ : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I))) *
      ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) * diagPlus (σ : ℂ) σ μ ν v w =
      diagPlus (σ : ℂ) σ μ ν v w := by
  by_cases h : μ = ν
  · subst h
    have h1 := phase_cancel hμ hμ t
    rw [div_self hμ.ne', Complex.ofReal_one, Complex.one_cpow, mul_one] at h1
    rw [h1, one_mul]
  · simp [diagPlus, h]

/-- **`‖F_t‖² = Σ_{k,l} b̄_k b_l (2 diag_{kl} + 2 R_{kl}(t))`.** -/
theorem norm_famL2_sq {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k)) (b : ι → ℂ) :
    ((‖famL2 hσ t s hμ v b‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ s, ∑ l ∈ s, conj (b k) * b l * linePair σ t (μ k) (μ l) (v k) (v l) := by
  have hF : ⟪famL2 hσ t s hμ v b, famL2 hσ t s hμ v b⟫_ℂ =
      ((‖famL2 hσ t s hμ v b‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [← hF, famL2, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_toDeckL2_toDeckL2,
    integral_inner_poincSeries_line hσ t (hμ k) (hμ l) (hv k) (hv l), map_mul, linePair]
  have h1 := phase_cancel (hμ k) (hμ l) t
  have h2 := phase_mul_diagPlus (N := N) (ν := μ l) (hμ k) σ t (v k) (v l)
  set P := conj (((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)))
  set Q := ((2 * Real.pi * μ l : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I))
  set E := (((μ l / μ k : ℝ)) : ℂ) ^ ((t : ℂ) * Complex.I)
  set D := diagPlus (σ : ℂ) σ (μ k) (μ l) (v k) (v l)
  set R := ∑' r : ReducedRow, rowWeightPlus (μ k) (μ l) (v k) (v l) r.1 *
    ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ k * μ l / rowSq r))
  calc conj (b k) * P * (b l * Q * (2 * D + 2 * (E * R)))
      = conj (b k) * b l * (2 * (P * Q * D) + 2 * ((P * Q * E) * R)) := by ring
    _ = conj (b k) * b l * (2 * D + 2 * R) := by rw [h1, h2, one_mul]

/-- `⟨u_j, F_t⟩ = 2 W̄(σ+it, ν_j) Ā_j(σ)`. -/
theorem inner_cuspEigenBasis_famL2 {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s : Finset ι) {μ : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k)) (b : ι → ℂ)
    (j : CuspEigenIndex N) :
    ⟪(cuspEigenBasis N j : DeckL2 N), famL2 hσ t s hμ v b⟫_ℂ =
      2 * conj (whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)) *
        conj (specCoeff j σ s μ v b) := by
  have hs : 1 < ((σ : ℂ) - t * Complex.I).re := by simpa using hσ
  have hconj : conj ((σ : ℂ) - t * Complex.I) = (σ : ℂ) + t * Complex.I := by
    simp [map_sub, Complex.conj_ofReal]
  rw [famL2, inner_sum, specCoeff, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hx : (0 : ℝ) < 2 * Real.pi * μ k := by have := hμ k; positivity
  have hxc : ((2 * Real.pi * μ k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [inner_smul_right, ← inner_conj_symm, inner_poincL2_cuspEigenBasis hs (hμ k) (hv k) j, hconj]
  simp only [map_mul, map_ofNat, Complex.conj_conj]
  rw [conj_ofReal_cpow hx.le, conj_ofReal_cpow hx.le]
  have hexp : ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) *
      ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (conj (-((σ : ℂ) + t * Complex.I - 1 / 2))) =
      ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (conj (-((σ : ℂ) - 1 / 2))) := by
    rw [← Complex.cpow_add _ _ hxc]
    congr 1
    simp only [map_neg, map_sub, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀,
      map_one, map_ofNat]
    ring
  calc b k * ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) *
        (2 * (conj (cuspCoeff j (μ k) (v k)) *
          ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (conj (-((σ : ℂ) + t * Complex.I - 1 / 2))) *
          conj (whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1))))
      = 2 * conj (whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)) *
        (b k * conj (cuspCoeff j (μ k) (v k)) *
          (((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)) *
          ((2 * Real.pi * μ k : ℝ) : ℂ) ^ (conj (-((σ : ℂ) + t * Complex.I - 1 / 2))))) := by ring
    _ = _ := by rw [hexp]

/-- **Bessel's inequality on the line**: `4 Σ_j |W(σ+it, ν_j)|² |A_j(σ)|² ≤ ‖F_t‖²`. -/
theorem summable_and_tsum_norm_whittMellin_sq_mul_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s : Finset ι)
    {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k))
    (b : ι → ℂ) :
    Summable (fun j : CuspEigenIndex N => 4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
      ‖specCoeff j σ s μ v b‖ ^ 2) ∧
    ∑' j : CuspEigenIndex N, 4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
      ‖specCoeff j σ s μ v b‖ ^ 2 ≤ ‖famL2 hσ t s hμ v b‖ ^ 2 := by
  have hpt : ∀ j : CuspEigenIndex N,
      ‖⟪(cuspEigenBasis N j : DeckL2 N), famL2 hσ t s hμ v b⟫_ℂ‖ ^ 2 =
        4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
          ‖specCoeff j σ s μ v b‖ ^ 2 := fun j => by
    rw [inner_cuspEigenBasis_famL2 hσ t s hμ hv b j, norm_mul, norm_mul, Complex.norm_conj,
      Complex.norm_conj, Complex.norm_two]
    ring
  have h := orthonormal_cuspEigenBasis (N := N)
  refine ⟨(h.inner_products_summable (x := famL2 hσ t s hμ v b)).congr hpt, ?_⟩
  simp_rw [← hpt]
  exact h.tsum_inner_products_le _

/-! ## Integration against `g_K` -/

/-- `∫ g_K`. -/
def gaussMass (K : ℝ) : ℝ := ∫ t : ℝ, gaussWeight K t

/-- The integrated pairing `2 diag ∫g_K + 2 Σ_{(c,d)} ⟨v, ρ(M)⁻¹w⟩ e((μd+νa)/c) c^{−2σ} Ψ_σ(X_c)`. -/
def geomRow (σ K μ ν : ℝ) (v w : DeckSpace N) : ℂ :=
  2 * diagPlus (σ : ℂ) σ μ ν v w * gaussMass K + 2 * ∑' r : ReducedRow,
    rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
      gaussKernel σ K (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))

/-- The bilinear geometric form `Σ_{k,l} b̄_k b_l geomRow_{kl}`. -/
def geomForm (σ K : ℝ) (s : Finset ι) (μ : ι → ℝ) (v : ι → DeckSpace N) (b : ι → ℂ) : ℂ :=
  ∑ k ∈ s, ∑ l ∈ s, conj (b k) * b l * geomRow σ K (μ k) (μ l) (v k) (v l)

theorem integrable_and_integral_gaussWeight_mul_linePair {σ K : ℝ} (hσ : 1 < σ) (hK : 0 < K)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (v w : DeckSpace N) :
    Integrable (fun t : ℝ => (gaussWeight K t : ℂ) * linePair σ t μ ν v w) ∧
      ∫ t : ℝ, (gaussWeight K t : ℂ) * linePair σ t μ ν v w = geomRow σ K μ ν v w := by
  obtain ⟨hint, heq⟩ := integral_gaussWeight_mul_rowSum hσ hK hμ hν v w
  have hg : Integrable (fun t : ℝ => (gaussWeight K t : ℂ)) := (integrable_gaussWeight hK).ofReal
  have hpt : (fun t : ℝ => (gaussWeight K t : ℂ) * linePair σ t μ ν v w) = fun t =>
      2 * diagPlus (σ : ℂ) σ μ ν v w * (gaussWeight K t : ℂ) + 2 * ((gaussWeight K t : ℂ) *
        ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
          sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) := by
    funext t; rw [linePair]; ring
  rw [hpt]
  refine ⟨(hg.const_mul _).add (hint.const_mul 2), ?_⟩
  rw [integral_add (hg.const_mul _) (hint.const_mul 2), integral_const_mul, integral_const_mul,
    heq, geomRow, gaussMass, integral_complex_ofReal]

/-- **The integrated Bessel inequality at `σ > 1`.** -/
theorem lintegral_bessel_le {σ K : ℝ} (hσ : 1 < σ) (hK : 0 < K) (s : Finset ι) {μ : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k)) (b : ι → ℂ) :
    ∑' j : CuspEigenIndex N, ∫⁻ t : ℝ, ENNReal.ofReal (gaussWeight K t *
      (4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j σ s μ v b‖ ^ 2)) ≤ ENNReal.ofReal (geomForm σ K s μ v b).re := by
  set a : CuspEigenIndex N → ℝ → ℝ := fun j t => gaussWeight K t *
    (4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 * ‖specCoeff j σ s μ v b‖ ^ 2)
    with ha
  have hg : Continuous (gaussWeight K) := by unfold gaussWeight; fun_prop
  have hmeas : ∀ j, Measurable (a j) := fun j =>
    hg.measurable.mul (((measurable_whittMellin_line (cuspEigenBasis_lam_nonneg j) hσ.le).norm.pow_const
      2).const_mul 4 |>.mul_const _)
  have hnn : ∀ j t, 0 ≤ a j t := fun j t => mul_nonneg (gaussWeight_nonneg K t) (by positivity)
  -- the geometric side as a function of `t`
  set G : ℝ → ℂ := fun t => ∑ k ∈ s, ∑ l ∈ s, conj (b k) * b l *
    ((gaussWeight K t : ℂ) * linePair σ t (μ k) (μ l) (v k) (v l)) with hG
  have hGint : Integrable G := integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    ((integrable_and_integral_gaussWeight_mul_linePair hσ hK (hμ k) (hμ l) (v k) (v l)).1.const_mul _)
  have hGval : ∫ t, G t = geomForm σ K s μ v b := by
    rw [hG, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      ((integrable_and_integral_gaussWeight_mul_linePair hσ hK (hμ k) (hμ l) (v k) (v l)).1.const_mul _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ =>
      ((integrable_and_integral_gaussWeight_mul_linePair hσ hK (hμ k) (hμ l) (v k) (v l)).1.const_mul _)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, (integrable_and_integral_gaussWeight_mul_linePair hσ hK (hμ k) (hμ l)
      (v k) (v l)).2]
  have hFG : ∀ t, gaussWeight K t * ‖famL2 hσ t s hμ v b‖ ^ 2 = (G t).re := fun t => by
    have h := congrArg Complex.re (norm_famL2_sq hσ t s hμ hv b)
    rw [Complex.ofReal_re] at h
    rw [h, hG, ← Complex.re_ofReal_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hFint : Integrable fun t => gaussWeight K t * ‖famL2 hσ t s hμ v b‖ ^ 2 := by
    simp_rw [hFG]; exact hGint.re
  calc ∑' j : CuspEigenIndex N, ∫⁻ t : ℝ, ENNReal.ofReal (a j t)
      = ∫⁻ t : ℝ, ∑' j : CuspEigenIndex N, ENNReal.ofReal (a j t) :=
        (lintegral_tsum fun j => (ENNReal.measurable_ofReal.comp (hmeas j)).aemeasurable).symm
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (∑' j : CuspEigenIndex N, a j t) := by
        refine lintegral_congr fun t => (ENNReal.ofReal_tsum_of_nonneg (fun j => hnn j t) ?_).symm
        simp only [ha]
        exact (summable_and_tsum_norm_whittMellin_sq_mul_le hσ t s hμ hv b).1.mul_left _
    _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal (gaussWeight K t * ‖famL2 hσ t s hμ v b‖ ^ 2) := by
        refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
        simp only [ha]
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (summable_and_tsum_norm_whittMellin_sq_mul_le hσ t s hμ hv b).2
          (gaussWeight_nonneg K t)
    _ = ENNReal.ofReal (∫ t : ℝ, gaussWeight K t * ‖famL2 hσ t s hμ v b‖ ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hFint
          (Eventually.of_forall fun t => mul_nonneg (gaussWeight_nonneg K t) (by positivity))).symm
    _ = ENNReal.ofReal (geomForm σ K s μ v b).re := by
        simp_rw [hFG]
        have h := integral_re hGint
        simp only [RCLike.re_to_complex] at h
        rw [h, hGval]

/-! ## The limit `σ ↓ 1` -/

theorem one_le_rowSq (r : ReducedRow) : 1 ≤ rowSq r := by
  have hc : (r.1.1 0 : ℤ) ≠ 0 := r.2.1
  have h1 : (1 : ℝ) ≤ |(r.1.1 0 : ℝ)| := by
    have := Int.one_le_abs hc
    exact_mod_cast this
  have h2 : (rowSq r) = |(r.1.1 0 : ℝ)| ^ 2 := (sq_abs _).symm
  rw [h2]; nlinarith

theorem continuous_specCoeff (j : CuspEigenIndex N) (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    (v : ι → DeckSpace N) (b : ι → ℂ) : Continuous fun σ : ℝ => specCoeff j σ s μ v b := by
  unfold specCoeff
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  have hx : ((2 * Real.pi * μ k : ℝ) : ℂ) ≠ 0 := by
    have := hμ k; exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi * μ k).ne'
  exact (by fun_prop : Continuous fun σ : ℝ => -((σ : ℂ) - 1 / 2)).const_cpow (Or.inl hx)

theorem tendsto_diagPlus {μ ν : ℝ} (hμ : 0 < μ) (v w : DeckSpace N) :
    Tendsto (fun σ : ℝ => diagPlus (σ : ℂ) σ μ ν v w) (𝓝 1) (𝓝 (diagPlus (1 : ℝ) (1 : ℝ) μ ν v w)) := by
  unfold diagPlus
  split_ifs with h
  · have hc : (1 / ((4 * Real.pi * μ : ℝ) : ℂ)) ≠ 0 :=
      one_div_ne_zero (by exact_mod_cast (by positivity : (0 : ℝ) < 4 * Real.pi * μ).ne')
    have hG : ContinuousAt Complex.Gamma ((((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) - 1)) := by
      refine (Complex.differentiableAt_Gamma _ fun m => ne_neg_nat_of_re_pos ?_ m).continuousAt
      simp
    refine ((((by fun_prop : Continuous fun σ : ℝ => (σ : ℂ) + σ - 1).const_cpow
      (Or.inl hc)).tendsto 1).mul (hG.tendsto.comp ((by fun_prop : Continuous fun σ : ℝ =>
        (σ : ℂ) + σ - 1).tendsto 1))).mul_const _
  · exact tendsto_const_nhds

theorem tendsto_geomRow {K μ ν : ℝ} (hK : 0 < K) (hμ : 0 < μ) (hν : 0 < ν) (v w : DeckSpace N) :
    Tendsto (fun σ : ℝ => geomRow σ K μ ν v w) (𝓝[>] 1) (𝓝 (geomRow 1 K μ ν v w)) := by
  unfold geomRow
  refine (((tendsto_diagPlus hμ v w).mono_left nhdsWithin_le_nhds).const_mul 2 |>.mul_const _).add
    (Tendsto.const_mul 2 ?_)
  set C : ℝ := ‖v‖ * ‖w‖ * (Real.pi * (4 * Real.pi * Real.sqrt (μ * ν)) * gaussSinhMass K)
  have hCm : 0 ≤ gaussSinhMass K := integral_nonneg fun w => abs_nonneg _
  refine tendsto_tsum_of_dominated_convergence (bound := fun r => C * rowSq r ^ (-(3 / 2 : ℝ)))
    ((summable_reducedRow_rpow (τ := 3 / 2) (by norm_num)).mul_left C) (fun r => ?_) ?_
  · have hq := rowSq_pos r
    have h1 : Tendsto (fun σ : ℝ => ((rowSq r ^ (-σ) : ℝ) : ℂ)) (𝓝[>] 1)
        (𝓝 ((rowSq r ^ (-(1 : ℝ)) : ℝ) : ℂ)) :=
      ((Complex.continuous_ofReal.tendsto _).comp
        (((Real.continuousAt_const_rpow hq.ne').comp continuous_neg.continuousAt).tendsto)).mono_left
        nhdsWithin_le_nhds
    have hX : 0 ≤ 4 * Real.pi * Real.sqrt (μ * ν / rowSq r) := by positivity
    exact (h1.const_mul _).mul (tendsto_gaussKernel hK hX)
  · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ) r
    have hq := rowSq_pos r
    have hq1 := one_le_rowSq r
    have hX : 0 ≤ 4 * Real.pi * Real.sqrt (μ * ν / rowSq r) := by positivity
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h1 := norm_rowWeightPlus_le μ ν v w r.1
    have h2 := norm_gaussKernel_le hσ.le hK hX
    have h3 : rowSq r ^ (-σ) ≤ rowSq r ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have h4 : Real.sqrt (μ * ν / rowSq r) = Real.sqrt (μ * ν) * rowSq r ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_div' _ hq.le, Real.sqrt_eq_rpow (rowSq r), Real.rpow_neg hq.le, div_eq_mul_inv]
    have h5 : rowSq r ^ (-(1 : ℝ)) * rowSq r ^ (-(1 / 2 : ℝ)) = rowSq r ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hq]; norm_num
    calc ‖rowWeightPlus μ ν v w r.1‖ * rowSq r ^ (-σ) *
          ‖gaussKernel σ K (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))‖
        ≤ ‖v‖ * ‖w‖ * rowSq r ^ (-(1 : ℝ)) *
          (Real.pi * (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)) * gaussSinhMass K) := by
          gcongr
      _ = C * (rowSq r ^ (-(1 : ℝ)) * rowSq r ^ (-(1 / 2 : ℝ))) := by rw [h4]; ring
      _ = C * rowSq r ^ (-(3 / 2 : ℝ)) := by rw [h5]

theorem tendsto_geomForm {K : ℝ} (hK : 0 < K) (s : Finset ι) {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k)
    (v : ι → DeckSpace N) (b : ι → ℂ) :
    Tendsto (fun σ : ℝ => geomForm σ K s μ v b) (𝓝[>] 1) (𝓝 (geomForm 1 K s μ v b)) :=
  tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ =>
    (tendsto_geomRow hK (hμ k) (hμ l) (v k) (v l)).const_mul _

theorem tsum_liminf_le_liminf_tsum {α : Type*} [Countable α] (F : ℕ → α → ENNReal) :
    ∑' a, liminf (fun n => F n a) atTop ≤ liminf (fun n => ∑' a, F n a) atTop := by
  letI : MeasurableSpace α := ⊤
  haveI : MeasurableSingletonClass α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have h := lintegral_liminf_le (μ := Measure.count) (f := F) (u := atTop)
    fun n => measurable_from_top
  simpa [lintegral_count] using h

/-- **The integrated Bessel inequality at `σ = 1`.** -/
theorem lintegral_bessel_le_one {K : ℝ} (hK : 0 < K) (s : Finset ι) {μ : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k)) (b : ι → ℂ) :
    ∑' j : CuspEigenIndex N, ∫⁻ t : ℝ, ENNReal.ofReal (gaussWeight K t *
      (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j 1 s μ v b‖ ^ 2)) ≤ ENNReal.ofReal (geomForm 1 K s μ v b).re := by
  set σn : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  have hσn : ∀ n, 1 < σn n := fun n => by simp only [σn]; have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                                          linarith
  have hσt : Tendsto σn atTop (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hσn⟩
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    simpa [σn] using this
  set F : ℕ → CuspEigenIndex N → ℝ → ENNReal := fun n j t => ENNReal.ofReal (gaussWeight K t *
    (4 * ‖whittMellin ((σn n : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
      ‖specCoeff j (σn n) s μ v b‖ ^ 2))
  set f : CuspEigenIndex N → ℝ → ENNReal := fun j t => ENNReal.ofReal (gaussWeight K t *
    (4 * ‖whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
      ‖specCoeff j 1 s μ v b‖ ^ 2))
  have hg : Continuous (gaussWeight K) := by unfold gaussWeight; fun_prop
  -- pointwise convergence for `t ≠ 0`
  have hconv : ∀ j, ∀ t : ℝ, t ≠ 0 → Tendsto (fun n => F n j t) atTop (𝓝 (f j t)) := by
    intro j t ht
    have hW : Tendsto (fun σ : ℝ => whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)) (𝓝 1)
        (𝓝 (whittMellin ((1 : ℝ) + t * Complex.I) (specParam j.1))) :=
      (continuousAt_whittMellin_specParam (cuspEigenBasis_lam_nonneg j) le_rfl (Or.inl ht)).tendsto.comp
        ((by fun_prop : Continuous fun σ : ℝ => (σ : ℂ) + t * Complex.I).tendsto 1)
    have hA := (continuous_specCoeff j s hμ v b).tendsto 1
    have h := ((((hW.norm.pow 2).const_mul 4).mul (hA.norm.pow 2)).const_mul (gaussWeight K t)).comp
      (hσt.mono_right nhdsWithin_le_nhds)
    exact ENNReal.tendsto_ofReal h
  have hmeasF : ∀ n j, Measurable (F n j) := fun n j =>
    ENNReal.measurable_ofReal.comp (hg.measurable.mul
      ((((measurable_whittMellin_line (cuspEigenBasis_lam_nonneg j) (hσn n).le).norm.pow_const
        2).const_mul 4).mul_const _))
  have hfatou : ∀ j, ∫⁻ t, f j t ≤ liminf (fun n => ∫⁻ t, F n j t) atTop := by
    intro j
    have hae : (fun t => f j t) =ᵐ[volume] fun t => liminf (fun n => F n j t) atTop := by
      have h0 : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
        rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]; exact measure_singleton 0
      filter_upwards [h0] with t ht
      exact ((hconv j t ht).liminf_eq).symm
    rw [lintegral_congr_ae hae]
    exact lintegral_liminf_le fun n => hmeasF n j
  have hgeom : Tendsto (fun n => ENNReal.ofReal (geomForm (σn n) K s μ v b).re) atTop
      (𝓝 (ENNReal.ofReal (geomForm 1 K s μ v b).re)) :=
    ENNReal.tendsto_ofReal ((Complex.continuous_re.tendsto _).comp
      ((tendsto_geomForm hK s hμ v b).comp hσt))
  calc ∑' j, ∫⁻ t, f j t ≤ ∑' j, liminf (fun n => ∫⁻ t, F n j t) atTop := ENNReal.tsum_le_tsum hfatou
    _ ≤ liminf (fun n => ∑' j, ∫⁻ t, F n j t) atTop := tsum_liminf_le_liminf_tsum _
    _ ≤ liminf (fun n => ENNReal.ofReal (geomForm (σn n) K s μ v b).re) atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => lintegral_bessel_le (hσn n) hK s hμ hv b)
    _ = ENNReal.ofReal (geomForm 1 K s μ v b).re := hgeom.liminf_eq

end

end GaloisForLFunctions.RHTower.DeckPointPair
