/-
# `(DC)` in several variables

Both halves of the determinant-defect completion law are packaged as one set equality for linear
operator pencils.  The graph closure and the completion fibre are stated locally along every line
through the origin, which is forced: the plain determinant is its trace series, so it only exists
near the origin, and `opSchattenDet_pencil_line` carries the spectral variable into the parameter.

The necessity half needs the coefficient convergence of the low-trace jets, which the one-variable
law now exposes; assembling the multivariable jet from the line restrictions uses the polynomiality
of the pencil power traces.  The sufficiency half needs no Vitali argument: the several-variable
construction prescribes the low power traces of the approximants *exactly*, so their low-trace
polynomial does not depend on the approximation index and the locally uniform convergence of the
plain determinants follows from that of the regularized ones.

Main results:
* `monomialFun_mem_span_clmPow`, `eval_homogeneousComponent_mem_span_clmPow` — the polarization
  bridge from homogeneous polynomials to powers of linear forms.
* `exists_uniform_schattenBound`, `exists_lineJet_of_locallyUniform` — the one-variable jet along a
  line, with its coefficient convergence.
* `eval_smul_of_isHomogeneous`, `tendstoUniformlyOn_mul_continuousOn`.
* `PencilGraphClosure`, `PencilCompletionFibre`.
* `pencilGraphClosure_eq_pencilCompletionFibre` — **`(DC)` in several variables**.
-/
import GaloisForLFunctions.HTGeometry.PencilMomentRealization
import GaloisForLFunctions.HTGeometry.DeterminantCompletionLaw
import GaloisForLFunctions.HTGeometry.PencilLowTraceJet
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open RHTower Metric ContinuousLinearMap

set_option linter.unusedSectionVars false

/-- **A monomial function of total degree `k` is a combination of `k`-th powers of linear
forms.** -/
theorem monomialFun_mem_span_clmPow {d k : ℕ} (a : Fin d →₀ ℕ) (ha : ∑ i, a i = k) :
    (fun v : Fin d → ℂ => ∏ i, (v i) ^ (a i))
      ∈ Submodule.span ℂ (clmPowSet (Fin d → ℂ) k) := by
  classical
  have hcard : Fintype.card ((i : Fin d) × Fin (a i)) = k := by
    rw [Fintype.card_sigma]
    simpa using ha
  obtain ⟨e, hedef⟩ : ∃ e : Fin k ≃ ((i : Fin d) × Fin (a i)),
    e = (Fintype.equivFinOfCardEq hcard).symm := ⟨_, rfl⟩
  have hprod : (fun v : Fin d → ℂ => ∏ i, (v i) ^ (a i))
      = fun v : Fin d → ℂ => ∏ r : Fin k,
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (e r).1) v := by
    funext v
    show (∏ i, (v i) ^ (a i)) = ∏ r : Fin k, v (e r).1
    rw [Equiv.prod_comp e (fun s : (i : Fin d) × Fin (a i) => v s.1), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun i _ => ?_
    show v i ^ a i = ∏ _y : Fin (a i), v i
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod]
  exact prod_clm_mem_span_clmPow
    (fun r => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (e r).1)

/-- **The homogeneous components of a polynomial are combinations of powers of linear forms.** -/
theorem eval_homogeneousComponent_mem_span_clmPow {d : ℕ} (k : ℕ)
    (Q : MvPolynomial (Fin d) ℂ) :
    (fun v : Fin d → ℂ => MvPolynomial.eval v (MvPolynomial.homogeneousComponent k Q))
      ∈ Submodule.span ℂ (clmPowSet (Fin d → ℂ) k) := by
  classical
  have hfun : (fun v : Fin d → ℂ => MvPolynomial.eval v
        (MvPolynomial.homogeneousComponent k Q))
      = ∑ a ∈ Q.support.filter (fun a => ∑ i ∈ a.support, a i = k),
        (MvPolynomial.coeff a Q) • (fun v : Fin d → ℂ => ∏ i, (v i) ^ (a i)) := by
    funext v
    rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPolynomial.eval_monomial, Pi.smul_apply, smul_eq_mul]
    congr 1
    exact Finsupp.prod_fintype a (fun n e => v n ^ e) (fun n => by rw [pow_zero])
  rw [hfun]
  refine Submodule.sum_mem _ fun a ha => ?_
  refine Submodule.smul_mem _ _ ?_
  rw [Finset.mem_filter] at ha
  refine monomialFun_mem_span_clmPow a ?_
  rw [← ha.2]
  exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
    simpa using Finsupp.notMem_support_iff.mp hi).symm


section LineJet

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A Schatten-convergent family has a uniform Schatten bound covering the limit. -/
theorem exists_uniform_schattenBound {p : ℕ} (hp : 0 < p)
    {A : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : ∀ n, MemSchattenClass (p : ℝ) (A n)) (hT : MemSchattenClass (p : ℝ) T)
    (htend : Tendsto (fun n => schattenNorm (p : ℝ) (A n - T)) atTop (nhds 0)) :
    ∃ C : ℝ, 1 ≤ C ∧ (∀ n, schattenNorm (p : ℝ) (A n) ≤ C) ∧
      schattenNorm (p : ℝ) T ≤ C := by
  classical
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hDmem : ∀ n, MemSchattenClass (p : ℝ) (A n - T) := by
    intro n
    rw [sub_eq_add_neg]
    exact memSchattenClass_add hpR (hA n) (memSchattenClass_neg hT)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ n, schattenNorm (p : ℝ) (A n - T) ≤ C₀ := by
    obtain ⟨C₀, hC₀⟩ := htend.bddAbove_range
    exact ⟨C₀, fun n => hC₀ ⟨n, rfl⟩⟩
  have hC₀0 : (0 : ℝ) ≤ C₀ := le_trans (schattenNorm_nonneg _ _) (hC₀ 0)
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      K = 2 ^ ((p : ℝ) + 1) * (C₀ ^ (p : ℝ) + schattenNorm (p : ℝ) T ^ (p : ℝ)) := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ,
      C = max 1 (max (K ^ (1 / (p : ℝ))) (schattenNorm (p : ℝ) T)) := ⟨_, rfl⟩
  have hC1 : (1 : ℝ) ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCT : schattenNorm (p : ℝ) T ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have htwo : (0 : ℝ) ≤ 2 ^ ((p : ℝ) + 1) := Real.rpow_nonneg (by norm_num) _
  refine ⟨C, hC1, fun n => ?_, hCT⟩
  have hsplit : schattenNorm (p : ℝ) (A n) ^ (p : ℝ)
      ≤ 2 ^ ((p : ℝ) + 1) * (schattenNorm (p : ℝ) (A n - T) ^ (p : ℝ)
        + schattenNorm (p : ℝ) T ^ (p : ℝ)) := by
    have h := schattenNorm_add_rpow_le hpR (hDmem n) hT
    rwa [show A n - T + T = A n by abel] at h
  have hmono : schattenNorm (p : ℝ) (A n - T) ^ (p : ℝ) ≤ C₀ ^ (p : ℝ) :=
    Real.rpow_le_rpow (schattenNorm_nonneg _ _) (hC₀ n) hpR.le
  have hAK : schattenNorm (p : ℝ) (A n) ^ (p : ℝ) ≤ K := by
    rw [hK]
    nlinarith [hsplit, hmono, htwo]
  have hnn : (0 : ℝ) ≤ schattenNorm (p : ℝ) (A n) := schattenNorm_nonneg _ _
  calc schattenNorm (p : ℝ) (A n)
      = (schattenNorm (p : ℝ) (A n) ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
        rw [← Real.rpow_mul hnn, mul_one_div, div_self hpR.ne', Real.rpow_one]
    _ ≤ K ^ (1 / (p : ℝ)) := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hAK (by positivity)
    _ ≤ C := by rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)

/-- **The one-variable jet along a line, with its coefficient convergence, from a Schatten-convergent
family.**  The uniform Schatten bound and the admissible radius are constructed internally. -/
theorem exists_lineJet_of_locallyUniform {p : ℕ} (hp : 0 < p)
    {A : ℕ → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hA : ∀ n, MemSchattenClass (p : ℝ) (A n)) (hT : MemSchattenClass (p : ℝ) T)
    (htend : Tendsto (fun n => schattenNorm (p : ℝ) (A n - T)) atTop (nhds 0))
    {r : ℝ} (hr0 : 0 < r) {G : ℂ → ℂ}
    (hlu : TendstoLocallyUniformlyOn (fun n z => opSchattenDet 1 (A n) z) G atTop
      (ball (0 : ℂ) r)) :
    ∃ (ρ : ℝ) (Q : Polynomial ℂ), 0 < ρ ∧ Q.natDegree ≤ p - 1 ∧ Q.coeff 0 = 0 ∧
      (∀ h : ℕ, Tendsto (fun n => (lowTracePoly p (A n)).coeff h) atTop (nhds (Q.coeff h))) ∧
      ∀ z ∈ ball (0 : ℂ) ρ, G z = opSchattenDet p T z * Complex.exp (Polynomial.eval z Q) := by
  classical
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hDmem : ∀ n, MemSchattenClass (p : ℝ) (A n - T) := by
    intro n
    rw [sub_eq_add_neg]
    exact memSchattenClass_add hpR (hA n) (memSchattenClass_neg hT)
  obtain ⟨C, hC1, hCA, hCT⟩ := exists_uniform_schattenBound hp hA hT htend
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  obtain ⟨r₁, hr₁def⟩ : ∃ r₁ : ℝ, r₁ = min r (1 / (4 * C)) := ⟨_, rfl⟩
  have hr₁0 : 0 < r₁ := by rw [hr₁def]; exact lt_min hr0 (by positivity)
  have hr₁r : r₁ ≤ r := by rw [hr₁def]; exact min_le_left _ _
  have hr₁B : r₁ * (2 * C) < 1 := by
    have h1 : r₁ ≤ 1 / (4 * C) := by rw [hr₁def]; exact min_le_right _ _
    have h2 : r₁ * (2 * C) ≤ (1 / (4 * C)) * (2 * C) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : (1 / (4 * C)) * (2 * C) = 1 / 2 := by field_simp; ring
    rw [h3] at h2
    linarith
  obtain ⟨ρ, Q, hρ0, -, hQdeg, hQ0, hQcoeff, hQval⟩ :=
    exists_poly_coeff_of_tendstoLocallyUniformlyOn_opSchattenDet hp hA hT hDmem hC1 hCA hCT
      htend hr₁0 hr₁B (hlu.mono (ball_subset_ball hr₁r))
  exact ⟨ρ, Q, hρ0, hQdeg, hQ0, hQcoeff, hQval⟩

end LineJet


theorem tendstoUniformlyOn_mul_continuousOn {X : Type*} [TopologicalSpace X]
    {F : ℕ → X → ℂ} {f g : X → ℂ} {K : Set X} (hK : IsCompact K)
    (hF : TendstoUniformlyOn F f atTop K) (hg : ContinuousOn g K) :
    TendstoUniformlyOn (fun n x => F n x * g x) (fun x => f x * g x) atTop K := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max C 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hMdef]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMb : ∀ x ∈ K, ‖g x‖ ≤ M := fun x hx =>
    le_trans (hC x hx) (by rw [hMdef]; exact le_max_left _ _)
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  filter_upwards [hF (ε / M) (by positivity)] with n hn x hx
  have hd : dist (f x * g x) (F n x * g x) = ‖g x‖ * dist (f x) (F n x) := by
    rw [dist_eq_norm, dist_eq_norm, ← sub_mul, norm_mul, mul_comm]
  rw [hd]
  have h1 := hn x hx
  have h2 : ‖g x‖ * dist (f x) (F n x) ≤ M * dist (f x) (F n x) :=
    mul_le_mul_of_nonneg_right (hMb x hx) dist_nonneg
  have h3 : M * dist (f x) (F n x) < M * (ε / M) := mul_lt_mul_of_pos_left h1 hM0
  rw [mul_div_cancel₀ _ hM0.ne'] at h3
  linarith

section Packaging

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closure of the finite-rank **pencil** determinant graph: finite-rank pencils converging to
the given pencil in the Schatten norm at every parameter, whose plain determinants converge locally
uniformly on a disc along every line through the origin. -/
def PencilGraphClosure (p d : ℕ) : Set ((Fin d → (H →L[ℂ] H)) × ((Fin d → ℂ) → ℂ)) :=
  {q | (∀ j, MemSchattenClass (p : ℝ) (q.1 j)) ∧
    ∃ F : ℕ → Fin d → (H →L[ℂ] H),
      (∀ n j, ∃ N : ℕ, HasRankLE (F n j) N) ∧
      (∀ v, Tendsto (fun n => schattenNorm (p : ℝ)
        (pencilOperator (F n) v - pencilOperator q.1 v)) atTop (nhds 0)) ∧
      (∀ v, ∃ r : ℝ, 0 < r ∧ TendstoLocallyUniformlyOn
        (fun n z => opSchattenDet 1 (pencilOperator (F n) v) z)
        (fun z => q.2 (fun i => z * v i)) atTop (ball (0 : ℂ) r))}

/-- The **completion fibre** of a pencil: the order-`p` regularized determinant times the
exponential of a multivariable jet of total degree below `p` with vanishing constant term. -/
def PencilCompletionFibre (p d : ℕ) : Set ((Fin d → (H →L[ℂ] H)) × ((Fin d → ℂ) → ℂ)) :=
  {q | (∀ j, MemSchattenClass (p : ℝ) (q.1 j)) ∧
    ∃ Q : MvPolynomial (Fin d) ℂ, Q.totalDegree ≤ p - 1 ∧
      MvPolynomial.eval (0 : Fin d → ℂ) Q = 0 ∧
      ∀ v : Fin d → ℂ, ∃ r : ℝ, 0 < r ∧ ∀ z ∈ ball (0 : ℂ) r,
        q.2 (fun i => z * v i)
          = opSchattenDet p (pencilOperator q.1 (fun i => z * v i)) 1 *
            Complex.exp (MvPolynomial.eval (fun i => z * v i) Q)}

variable {H}

set_option maxHeartbeats 1000000 in
/-- **Necessity in several variables.**  Every member of the pencil graph closure lies in the
completion fibre. -/
theorem pencilGraphClosure_subset_pencilCompletionFibre {p d : ℕ} (hp : 0 < p) :
    PencilGraphClosure H p d ⊆ PencilCompletionFibre H p d := by
  classical
  rintro ⟨T, G⟩ ⟨hT, F, hrank, hsch, hlu⟩
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hNn : ∀ n : ℕ, ∃ N : ℕ, ∀ j, HasRankLE (F n j) N := by
    intro n
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ j, HasRankLE (F n j) M := by
      choose Nj hNj using hrank n
      refine ⟨Finset.univ.sup Nj, fun j => ?_⟩
      obtain ⟨W, hW, hle, hmem⟩ := hNj j
      exact ⟨W, hW, le_trans hle (Finset.le_sup (Finset.mem_univ j)), hmem⟩
    exact ⟨M, hM⟩
  choose N hN using hNn
  have hFmem : ∀ (n : ℕ) (v : Fin d → ℂ),
      MemSchattenClass (p : ℝ) (pencilOperator (F n) v) := by
    intro n v
    exact memSchattenClass_pencilOperator hpR (fun j => memSchattenClass_of_hasRankLE hpR
      (hN n j)) v
  have hTmem : ∀ v, MemSchattenClass (p : ℝ) (pencilOperator T v) :=
    fun v => memSchattenClass_pencilOperator hpR hT v
  have hline : ∀ v : Fin d → ℂ, ∃ (ρ : ℝ) (Qv : Polynomial ℂ), 0 < ρ ∧
      Qv.natDegree ≤ p - 1 ∧ Qv.coeff 0 = 0 ∧
      (∀ h : ℕ, Tendsto (fun n => (lowTracePoly p (pencilOperator (F n) v)).coeff h) atTop
        (nhds (Qv.coeff h))) ∧
      ∀ z ∈ ball (0 : ℂ) ρ, G (fun i => z * v i)
        = opSchattenDet p (pencilOperator T v) z * Complex.exp (Polynomial.eval z Qv) := by
    intro v
    obtain ⟨r, hr0, hlv⟩ := hlu v
    exact exists_lineJet_of_locallyUniform hp (fun n => hFmem n v) (hTmem v) (hsch v) hr0 hlv
  choose ρ Qv hρ hQvdeg hQv0 hQvcoeff hQvval using hline
  have hcoeffMv : ∀ (v : Fin d → ℂ) (h : ℕ),
      Tendsto (fun n => (polynomialLineRestrictionLineRestrict v (lowTraceMv p (F n))).coeff h)
        atTop (nhds ((Qv v).coeff h)) := by
    intro v h
    have heq : ∀ n, polynomialLineRestrictionLineRestrict v (lowTraceMv p (F n))
        = lowTracePoly p (pencilOperator (F n) v) := fun n => lineRestrict_lowTraceMv (hN n) p v
    simp only [heq]
    exact hQvcoeff v h
  have hg : ∀ v : Fin d → ℂ,
      Tendsto (fun n => MvPolynomial.eval v (lowTraceMv p (F n))) atTop
        (nhds (Polynomial.eval 1 (Qv v))) := by
    intro v
    exact tendsto_eval_of_line_coeff (d := p - 1)
      (fun n => totalDegree_lowTraceMv_le p (F n)) v (hQvdeg v) (hcoeffMv v)
  obtain ⟨Q, hQdeg, hQeval⟩ := exists_mvPolynomial_of_tendsto_pointwise
    (fun n => totalDegree_lowTraceMv_le p (F n)) hg
  refine ⟨hT, Q, hQdeg, ?_, ?_⟩
  · rw [hQeval 0]
    exact eval_zero_eq_zero_of_tendsto (fun n => eval_zero_lowTraceMv p (F n)) hg
  · intro v
    refine ⟨ρ v, hρ v, fun z hz => ?_⟩
    have hval := hQvval v z hz
    have hjet : Polynomial.eval z (Qv v) = MvPolynomial.eval (fun i => z * v i) Q := by
      have h1 : Tendsto (fun n =>
          Polynomial.eval z (polynomialLineRestrictionLineRestrict v (lowTraceMv p (F n))))
          atTop (nhds (Polynomial.eval z (Qv v))) :=
        tendsto_eval_of_tendsto_coeff (N := p - 1)
          (fun n => natDegree_lineRestrict_le v (totalDegree_lowTraceMv_le p (F n)))
          (hQvdeg v) (hcoeffMv v) z
      have h2 : Tendsto (fun n =>
          Polynomial.eval z (polynomialLineRestrictionLineRestrict v (lowTraceMv p (F n))))
          atTop (nhds (MvPolynomial.eval (fun i => z * v i) Q)) := by
        have hres : ∀ n, Polynomial.eval z
            (polynomialLineRestrictionLineRestrict v (lowTraceMv p (F n)))
            = MvPolynomial.eval (fun i => z * v i) (lowTraceMv p (F n)) :=
          fun n => eval_lineRestrict v (lowTraceMv p (F n)) z
        simp only [hres]
        rw [hQeval (fun i => z * v i)]
        exact hg (fun i => z * v i)
      exact tendsto_nhds_unique h1 h2
    show G (fun i => z * v i) = _
    rw [hval, hjet, opSchattenDet_pencil_line]


/-- A homogeneous polynomial scales like a power under dilation of the argument. -/
theorem eval_smul_of_isHomogeneous {d n : ℕ} {φ : MvPolynomial (Fin d) ℂ}
    (h : φ.IsHomogeneous n) (z : ℂ) (v : Fin d → ℂ) :
    MvPolynomial.eval (fun i => z * v i) φ = z ^ n * MvPolynomial.eval v φ := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hdeg : ∑ i, a i = n := by
    have hw := h (MvPolynomial.mem_support_iff.mp ha)
    rw [Finsupp.weight_apply] at hw
    simp only [Pi.one_apply, smul_eq_mul, mul_one] at hw
    rw [← hw, Finsupp.sum]
    exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      simpa using Finsupp.notMem_support_iff.mp hi).symm
  rw [← hdeg, Finset.prod_congr rfl (fun i _ => mul_pow z (v i) (a i)),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

set_option maxHeartbeats 1000000 in
/-- **Sufficiency in several variables.**  Every member of the completion fibre lies in the pencil
graph closure. -/
theorem pencilCompletionFibre_subset_pencilGraphClosure {p d : ℕ}
    (hH : ¬ FiniteDimensional ℂ H) (hp : 0 < p) :
    PencilCompletionFibre H p d ⊆ PencilGraphClosure H p d := by
  classical
  rintro ⟨T, G⟩ ⟨hT, Q, hQdeg, hQ0, hQval⟩
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → (Fin d → ℂ) → ℂ,
    P = fun k v => MvPolynomial.eval v (MvPolynomial.homogeneousComponent k Q) := ⟨_, rfl⟩
  have hPspan : ∀ k, 1 ≤ k → k ≤ p - 1 →
      P k ∈ Submodule.span ℂ (clmPowSet (Fin d → ℂ) k) := by
    intro k _ _
    rw [hPdef]
    exact eval_homogeneousComponent_mem_span_clmPow k Q
  obtain ⟨F, hrank, hsch, hlow⟩ := exists_finiteRankPencil_tendsto_lowTrace hH hp hT P hPspan
  refine ⟨hT, F, hrank, hsch, ?_⟩
  intro v
  have hNn : ∀ n : ℕ, ∃ N : ℕ, ∀ j, HasRankLE (F n j) N := by
    intro n
    choose Nj hNj using hrank n
    refine ⟨Finset.univ.sup Nj, fun j => ?_⟩
    obtain ⟨W, hW, hle, hmem⟩ := hNj j
    exact ⟨W, hW, le_trans hle (Finset.le_sup (Finset.mem_univ j)), hmem⟩
  choose N hN using hNn
  have hFmem : ∀ n, MemSchattenClass (p : ℝ) (pencilOperator (F n) v) :=
    fun n => memSchattenClass_pencilOperator_of_hasRankLE hpR (hN n) v
  have hTmem : MemSchattenClass (p : ℝ) (pencilOperator T v) :=
    memSchattenClass_pencilOperator hpR hT v
  have hDmem : ∀ n, MemSchattenClass (p : ℝ) (pencilOperator (F n) v - pencilOperator T v) := by
    intro n
    rw [sub_eq_add_neg]
    exact memSchattenClass_add hpR (hFmem n) (memSchattenClass_neg hTmem)
  obtain ⟨C, hC1, hCA, hCT⟩ := exists_uniform_schattenBound hp hFmem hTmem (hsch v)
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  obtain ⟨r, hr0, hval⟩ := hQval v
  obtain ⟨r₁, hr₁def⟩ : ∃ r₁ : ℝ, r₁ = min r (1 / (4 * C)) := ⟨_, rfl⟩
  have hr₁0 : 0 < r₁ := by rw [hr₁def]; exact lt_min hr0 (by positivity)
  have hr₁r : r₁ ≤ r := by rw [hr₁def]; exact min_le_left _ _
  have hr₁B : r₁ * (2 * C) < 1 := by
    have h1 : r₁ ≤ 1 / (4 * C) := by rw [hr₁def]; exact min_le_right _ _
    have h2 : r₁ * (2 * C) ≤ (1 / (4 * C)) * (2 * C) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : (1 / (4 * C)) * (2 * C) = 1 / 2 := by field_simp; ring
    rw [h3] at h2
    linarith
  have hsmall : ∀ z ∈ ball (0 : ℂ) r₁, ‖z‖ * (2 * C) < 1 := by
    intro z hz
    have hzr : ‖z‖ < r₁ := by simpa using mem_ball_zero_iff.mp hz
    have : ‖z‖ * (2 * C) < r₁ * (2 * C) := mul_lt_mul_of_pos_right hzr (by linarith)
    linarith
  -- the low-trace polynomial of the approximants does not depend on `n`
  have hz0 : ∀ z : ℂ, MvPolynomial.eval (fun i => z * v i)
      (MvPolynomial.homogeneousComponent 0 Q) = 0 := by
    intro z
    have hc0 : MvPolynomial.homogeneousComponent 0 Q
        = MvPolynomial.C (MvPolynomial.coeff 0 Q) := by
      simp [MvPolynomial.homogeneousComponent_zero]
    have hcoeff : MvPolynomial.coeff 0 Q = 0 := by
      have hcc : MvPolynomial.coeff 0 Q = MvPolynomial.constantCoeff Q := rfl
      rw [hcc, ← hQ0]
      simp
    rw [hc0, hcoeff, map_zero, map_zero]
  have hsum : ∀ z : ℂ, MvPolynomial.eval (fun i => z * v i) Q
      = ∑ m ∈ Finset.Ico 1 p, MvPolynomial.eval (fun i => z * v i)
        (MvPolynomial.homogeneousComponent m Q) := by
    intro z
    have hfull : MvPolynomial.eval (fun i => z * v i) Q
        = ∑ m ∈ Finset.range (Q.totalDegree + 1), MvPolynomial.eval (fun i => z * v i)
          (MvPolynomial.homogeneousComponent m Q) := by
      conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent Q]
      rw [map_sum]
    have hup : ∑ m ∈ Finset.range (Q.totalDegree + 1), MvPolynomial.eval (fun i => z * v i)
        (MvPolynomial.homogeneousComponent m Q)
        = ∑ m ∈ Finset.range p, MvPolynomial.eval (fun i => z * v i)
          (MvPolynomial.homogeneousComponent m Q) := by
      refine Finset.sum_subset ?_ ?_
      · intro m hm
        rw [Finset.mem_range] at hm ⊢
        omega
      · intro m _ hm
        rw [Finset.mem_range] at hm
        rw [MvPolynomial.homogeneousComponent_eq_zero m Q (by omega), map_zero]
    have hlow0 : ∑ m ∈ Finset.range p, MvPolynomial.eval (fun i => z * v i)
        (MvPolynomial.homogeneousComponent m Q)
        = ∑ m ∈ Finset.Ico 1 p, MvPolynomial.eval (fun i => z * v i)
          (MvPolynomial.homogeneousComponent m Q) := by
      rw [Finset.range_eq_Ico]
      refine (Finset.sum_subset (Finset.Ico_subset_Ico (by omega) le_rfl) ?_).symm
      intro m hm hmn
      rw [Finset.mem_Ico] at hm hmn
      have : m = 0 := by omega
      subst this
      exact hz0 z
    rw [hfull, hup, hlow0]
  have hjet : ∀ (n : ℕ) (z : ℂ),
      Polynomial.eval z (lowTracePoly p (pencilOperator (F n) v))
        = MvPolynomial.eval (fun i => z * v i) Q := by
    intro n z
    rw [lowTracePoly, Polynomial.eval_finsetSum, hsum z]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [Finset.mem_Ico] at hm
    rw [hlow n v m hm.1 (by omega),
      eval_smul_of_isHomogeneous (MvPolynomial.homogeneousComponent_isHomogeneous m Q) z v,
      hPdef]
    have hmne : ((m : ℕ) : ℂ) ≠ 0 := by
      have hmpos : 0 < m := hm.1
      exact Nat.cast_ne_zero.mpr (by omega)
    field_simp
  -- locally uniform convergence of the plain determinants
  refine ⟨r₁, hr₁0, ?_⟩
  have hdetp := tendstoLocallyUniformlyOn_opSchattenDet (r := r₁) hp hFmem hTmem hDmem hC1
    hCA hCT (hsch v) hr₁B
  have hfact : ∀ (n : ℕ), ∀ z ∈ ball (0 : ℂ) r₁,
      opSchattenDet 1 (pencilOperator (F n) v) z
        = opSchattenDet p (pencilOperator (F n) v) z *
          Complex.exp (MvPolynomial.eval (fun i => z * v i) Q) := by
    intro n z hz
    rw [opSchattenDet_one_eq_mul_exp_lowTracePoly hp (hFmem n) hC1 (hCA n) (hsmall z hz),
      hjet n z]
  have hlimit : ∀ z ∈ ball (0 : ℂ) r₁,
      G (fun i => z * v i)
        = opSchattenDet p (pencilOperator T v) z *
          Complex.exp (MvPolynomial.eval (fun i => z * v i) Q) := by
    intro z hz
    have hval' : G (fun i => z * v i)
        = opSchattenDet p (pencilOperator T (fun i => z * v i)) 1 *
          Complex.exp (MvPolynomial.eval (fun i => z * v i) Q) :=
      hval z (ball_subset_ball hr₁r hz)
    rw [hval', opSchattenDet_pencil_line]
  have hgcont : ContinuousOn
      (fun z : ℂ => Complex.exp (MvPolynomial.eval (fun i => z * v i) Q)) (ball (0 : ℂ) r₁) := by
    refine Complex.continuous_exp.comp_continuousOn ?_
    exact (MvPolynomial.continuous_eval Q).comp_continuousOn
      (continuousOn_pi.mpr fun i => continuousOn_id.mul continuousOn_const)
  have hprod : TendstoLocallyUniformlyOn
      (fun n z => opSchattenDet p (pencilOperator (F n) v) z *
        Complex.exp (MvPolynomial.eval (fun i => z * v i) Q))
      (fun z => opSchattenDet p (pencilOperator T v) z *
        Complex.exp (MvPolynomial.eval (fun i => z * v i) Q)) atTop (ball (0 : ℂ) r₁) := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball] at hdetp ⊢
    intro K hKs hK
    exact tendstoUniformlyOn_mul_continuousOn hK (hdetp K hKs hK) (hgcont.mono hKs)
  refine TendstoLocallyUniformlyOn.congr ?_ (fun n z hz => (hfact n z hz).symm)
  exact TendstoLocallyUniformlyOn.congr_right hprod (fun z hz => (hlimit z hz).symm)


/-- **`(DC)` in several variables.**  The closure of the finite-rank pencil determinant graph is
exactly the completion fibre: the order-`p` regularized determinant times the exponential of a
multivariable jet of total degree below `p` with vanishing constant term. -/
theorem pencilGraphClosure_eq_pencilCompletionFibre {p d : ℕ}
    (hH : ¬ FiniteDimensional ℂ H) (hp : 0 < p) :
    PencilGraphClosure H p d = PencilCompletionFibre H p d :=
  Set.eq_of_subset_of_subset (pencilGraphClosure_subset_pencilCompletionFibre hp)
    (pencilCompletionFibre_subset_pencilGraphClosure hH hp)

end Packaging

end GaloisForLFunctions.HTGeometry

end
