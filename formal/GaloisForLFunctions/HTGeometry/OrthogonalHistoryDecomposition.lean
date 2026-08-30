import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Orthogonal history decomposition along a decreasing observation tower

For a decreasing chain of orthogonally complemented subspaces starting at the whole space, every
vector splits into its stage-`n` observed part and the vertical residuals produced at each step.
The residuals are pairwise orthogonal and orthogonal to every later stage, the decomposition
telescopes, and the induced analysis map is a linear isometry — so the observed endpoint together
with all vertical currents is an exact, closed, proper encoding of the source vector.
-/

open scoped BigOperators InnerProductSpace ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

variable (V : ℕ → Submodule 𝕜 E) [∀ k, (V k).HasOrthogonalProjection]

/-- `(PMP.17)`  The observed part of `f` at stage `k`. -/
def historyStage (f : E) (k : ℕ) : E := (V k).starProjection f

/-- `(PMP.17)`  The vertical information current produced between stages `k` and `k+1`. -/
def historyResidual (f : E) (k : ℕ) : E := historyStage V f k - historyStage V f (k + 1)

variable {V}

omit [CompleteSpace E] in
theorem historyStage_mem (f : E) (k : ℕ) : historyStage V f k ∈ V k :=
  Submodule.starProjection_apply_mem _ f

omit [CompleteSpace E] in
theorem historyResidual_mem (f : E) (k : ℕ) (hV : Antitone V) :
    historyResidual V f k ∈ V k :=
  Submodule.sub_mem _ (historyStage_mem f k) (hV (Nat.le_succ k) (historyStage_mem f (k + 1)))

omit [CompleteSpace E] in
theorem historyStage_succ (hV : Antitone V) (f : E) (k : ℕ) :
    historyStage V f (k + 1) = (V (k + 1)).starProjection (historyStage V f k) := by
  rw [historyStage, historyStage, ← ContinuousLinearMap.comp_apply,
    Submodule.starProjection_comp_starProjection_of_le (hV (Nat.le_succ k))]

omit [CompleteSpace E] in
/-- The residual at step `k` is orthogonal to every vector of the next stage. -/
theorem inner_historyResidual_eq_zero (hV : Antitone V) (f : E) (k : ℕ) {w : E}
    (hw : w ∈ V (k + 1)) : inner 𝕜 (historyResidual V f k) w = 0 := by
  rw [historyResidual, historyStage_succ hV f k]
  exact Submodule.starProjection_inner_eq_zero _ _ hw

omit [CompleteSpace E] in
theorem inner_historyResidual_historyStage (hV : Antitone V) (f : E) {j k : ℕ} (hjk : j < k) :
    inner 𝕜 (historyResidual V f j) (historyStage V f k) = 0 :=
  inner_historyResidual_eq_zero hV f j (hV hjk (historyStage_mem f k))

omit [CompleteSpace E] in
theorem inner_historyResidual_historyResidual (hV : Antitone V) (f : E) {j k : ℕ} (hjk : j < k) :
    inner 𝕜 (historyResidual V f j) (historyResidual V f k) = 0 :=
  inner_historyResidual_eq_zero hV f j (hV hjk (historyResidual_mem f k hV))

omit [CompleteSpace E] in
/-- `(PMP.18)`  The observed endpoint plus the vertical currents telescope to the source. -/
theorem historyStage_add_sum_residual (f : E) (n : ℕ) :
    historyStage V f n + ∑ k ∈ Finset.range n, historyResidual V f k = historyStage V f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, historyResidual]
      abel

omit [CompleteSpace E] in
theorem historyStage_zero (hV0 : V 0 = ⊤) (f : E) : historyStage V f 0 = f :=
  Submodule.starProjection_eq_self_iff.mpr (by rw [hV0]; exact Submodule.mem_top)

omit [CompleteSpace E] in
/-- `(PMP.18)`  Exact reconstruction of the source vector. -/
theorem eq_historyStage_add_sum_residual (hV0 : V 0 = ⊤) (f : E) (n : ℕ) :
    f = historyStage V f n + ∑ k ∈ Finset.range n, historyResidual V f k := by
  rw [historyStage_add_sum_residual f n, historyStage_zero hV0 f]

omit [CompleteSpace E] in
/-- `(PMP.19)`  The exact energy split of a finite observation history. -/
theorem norm_sq_eq_historyStage_add_sum (hV : Antitone V) (hV0 : V 0 = ⊤) (f : E) (n : ℕ) :
    ‖f‖ ^ 2 = ‖historyStage V f n‖ ^ 2
      + ∑ k ∈ Finset.range n, ‖historyResidual V f k‖ ^ 2 := by
  induction n with
  | zero => simp [historyStage_zero hV0 f]
  | succ n ih =>
      have hsplit : historyStage V f n = historyStage V f (n + 1) + historyResidual V f n := by
        rw [historyResidual]; abel
      have horth : inner 𝕜 (historyStage V f (n + 1)) (historyResidual V f n) = 0 := by
        have := inner_historyResidual_eq_zero hV f n (historyStage_mem f (n + 1))
        rw [← inner_conj_symm] at this
        simpa using congrArg (starRingEnd 𝕜) this
      have hpy : ‖historyStage V f n‖ ^ 2
          = ‖historyStage V f (n + 1)‖ ^ 2 + ‖historyResidual V f n‖ ^ 2 := by
        rw [hsplit]
        simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (historyStage V f (n + 1)) (historyResidual V f n) horth
      rw [ih, hpy, Finset.sum_range_succ]
      ring

/-! ## The finite analysis map -/

variable (V)

/-- `(PMP.20)`, `(PMP.21)`  The analysis map: observed endpoint in slot `0`, vertical currents
afterwards. -/
def historyAnalysis (n : ℕ) : E →L[𝕜] PiLp 2 (fun _ : Fin (n + 1) => E) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : Fin (n + 1) => E)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (Fin.cons ((V n).starProjection)
      fun k : Fin n => (V k).starProjection - (V (k + 1)).starProjection)

variable {V}

omit [CompleteSpace E] in
theorem historyAnalysis_apply_zero (n : ℕ) (f : E) :
    (historyAnalysis V n f).ofLp 0 = historyStage V f n := rfl

omit [CompleteSpace E] in
theorem historyAnalysis_apply_succ (n : ℕ) (f : E) (k : Fin n) :
    (historyAnalysis V n f).ofLp k.succ = historyResidual V f k := rfl

omit [CompleteSpace E] in
/-- `(PMP.19)`, `(PMP.21)`  The analysis map is a linear isometry. -/
theorem norm_historyAnalysis (hV : Antitone V) (hV0 : V 0 = ⊤) (n : ℕ) (f : E) :
    ‖historyAnalysis V n f‖ = ‖f‖ := by
  have hsq : ‖historyAnalysis V n f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, norm_sq_eq_historyStage_add_sum hV hV0 f n]
    congr 1
    rw [show (fun i : Fin n => ‖((historyAnalysis V n) f).ofLp i.succ‖ ^ 2)
      = fun i : Fin n => ‖historyResidual V f i‖ ^ 2 from rfl]
    exact Fin.sum_univ_eq_sum_range (fun k => ‖historyResidual V f k‖ ^ 2) n
  have h1 : 0 ≤ ‖historyAnalysis V n f‖ := norm_nonneg _
  have h2 : 0 ≤ ‖f‖ := norm_nonneg _
  nlinarith [hsq]

/-- `(PMP.21)`  The analysis map as a linear isometry. -/
def historyIsometry (hV : Antitone V) (hV0 : V 0 = ⊤) (n : ℕ) :
    E →ₗᵢ[𝕜] PiLp 2 (fun _ : Fin (n + 1) => E) where
  toLinearMap := (historyAnalysis V n).toLinearMap
  norm_map' := norm_historyAnalysis hV hV0 n

omit [CompleteSpace E] in
theorem historyIsometry_injective (hV : Antitone V) (hV0 : V 0 = ⊤) (n : ℕ) :
    Function.Injective (historyIsometry hV hV0 n) :=
  (historyIsometry hV hV0 n).injective

/-- `(PMP.21)`  The analysis map is a closed embedding, hence topologically proper onto its
image. -/
theorem historyIsometry_isClosedEmbedding (hV : Antitone V) (hV0 : V 0 = ⊤) (n : ℕ) :
    Topology.IsClosedEmbedding (historyIsometry hV hV0 n) :=
  (historyIsometry hV hV0 n).isometry.isClosedEmbedding

/-! ## Infinite observation histories -/

omit [CompleteSpace E] in
theorem historyStage_sub_eq_sum (f : E) {a b : ℕ} (hab : a ≤ b) :
    historyStage V f a - historyStage V f b
      = ∑ k ∈ Finset.Ico a b, historyResidual V f k := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab, ← ih, historyResidual]
      abel

omit [CompleteSpace E] in
theorem inner_historyStage_sub (hV : Antitone V) (f : E) {a b : ℕ} (hab : a ≤ b) :
    inner 𝕜 (historyStage V f b) (historyStage V f a - historyStage V f b) = 0 := by
  rw [historyStage_sub_eq_sum f hab, inner_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k + 1 ≤ b := (Finset.mem_Ico.mp hk).2
  have h := inner_historyResidual_eq_zero hV f k (hV hk' (historyStage_mem f b))
  rw [← inner_conj_symm] at h
  simpa using congrArg (starRingEnd 𝕜) h

omit [CompleteSpace E] in
theorem norm_sq_historyStage_sub (hV : Antitone V) (f : E) {a b : ℕ} (hab : a ≤ b) :
    ‖historyStage V f a - historyStage V f b‖ ^ 2
      = ‖historyStage V f a‖ ^ 2 - ‖historyStage V f b‖ ^ 2 := by
  have hsplit : historyStage V f a
      = historyStage V f b + (historyStage V f a - historyStage V f b) := by abel
  have hpy : ‖historyStage V f a‖ ^ 2
      = ‖historyStage V f b‖ ^ 2 + ‖historyStage V f a - historyStage V f b‖ ^ 2 := by
    rw [hsplit]
    simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (historyStage V f b) (historyStage V f a - historyStage V f b)
      (inner_historyStage_sub hV f hab)
  linarith

omit [CompleteSpace E] in
theorem norm_historyStage_antitone (hV : Antitone V) (f : E) :
    Antitone fun n => ‖historyStage V f n‖ ^ 2 := by
  refine antitone_nat_of_succ_le fun n => ?_
  have := norm_sq_historyStage_sub hV f (Nat.le_succ n)
  nlinarith [sq_nonneg ‖historyStage V f n - historyStage V f (n + 1)‖]

omit [CompleteSpace E] in
theorem sum_norm_sq_residual_le (hV : Antitone V) (hV0 : V 0 = ⊤) (f : E) (n : ℕ) :
    ∑ k ∈ Finset.range n, ‖historyResidual V f k‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have h := norm_sq_eq_historyStage_add_sum hV hV0 f n
  nlinarith [sq_nonneg ‖historyStage V f n‖]

omit [CompleteSpace E] in
theorem summable_norm_sq_residual (hV : Antitone V) (hV0 : V 0 = ⊤) (f : E) :
    Summable fun k => ‖historyResidual V f k‖ ^ 2 :=
  summable_of_sum_range_le (fun _ => by positivity) (sum_norm_sq_residual_le hV hV0 f)

omit [CompleteSpace E] in
theorem cauchySeq_historyStage (hV : Antitone V) (_hV0hV0 : V 0 = ⊤) (f : E) :
    CauchySeq fun n => historyStage V f n := by
  have hmono : Antitone fun n => ‖historyStage V f n‖ ^ 2 := norm_historyStage_antitone hV f
  have hbdd : ∀ n, (0 : ℝ) ≤ ‖historyStage V f n‖ ^ 2 := fun n => by positivity
  have hL := tendsto_atTop_ciInf hmono ⟨0, fun x ⟨n, hn⟩ => hn ▸ hbdd n⟩
  have hCauchy := hL.cauchySeq
  rw [Metric.cauchySeq_iff'] at hCauchy ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hCauchy (ε ^ 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hdist := hN n hn
  rw [Real.dist_eq, abs_lt] at hdist
  have hkey : ‖historyStage V f n - historyStage V f N‖ ^ 2 < ε ^ 2 := by
    rw [norm_sub_rev, norm_sq_historyStage_sub hV f hn]
    linarith [hdist.1, hdist.2]
  have hlt : ‖historyStage V f n - historyStage V f N‖ < ε := by
    nlinarith [norm_nonneg (historyStage V f n - historyStage V f N), hε.le]
  simpa [dist_eq_norm] using hlt

variable (V)

/-- `(PMP.23)`  The tail limit of the observed stages. -/
def historyLimit (f : E) : E := Filter.limUnder Filter.atTop fun n => historyStage V f n

variable {V}

theorem tendsto_historyStage (hV : Antitone V) (hV0 : V 0 = ⊤) (f : E) :
    Filter.Tendsto (fun n => historyStage V f n) Filter.atTop (nhds (historyLimit V f)) :=
  (cauchySeq_historyStage hV hV0 f).tendsto_limUnder

/-- `(PMP.24)`  Exact energy split of an infinite observation history. -/
theorem norm_sq_eq_historyLimit_add_tsum (hV : Antitone V) (hV0 : V 0 = ⊤) (f : E) :
    ‖f‖ ^ 2 = ‖historyLimit V f‖ ^ 2 + ∑' k, ‖historyResidual V f k‖ ^ 2 := by
  have hstage : Filter.Tendsto (fun n => ‖historyStage V f n‖ ^ 2) Filter.atTop
      (nhds (‖historyLimit V f‖ ^ 2)) := by
    exact ((tendsto_historyStage hV hV0 f).norm).pow 2
  have hsum : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, ‖historyResidual V f k‖ ^ 2)
      Filter.atTop (nhds (∑' k, ‖historyResidual V f k‖ ^ 2)) :=
    (summable_norm_sq_residual hV hV0 f).hasSum.tendsto_sum_nat
  have hconst : Filter.Tendsto (fun n : ℕ => ‖f‖ ^ 2) Filter.atTop (nhds (‖f‖ ^ 2)) :=
    tendsto_const_nhds
  have heq : ∀ n, ‖f‖ ^ 2 = ‖historyStage V f n‖ ^ 2
      + ∑ k ∈ Finset.range n, ‖historyResidual V f k‖ ^ 2 :=
    norm_sq_eq_historyStage_add_sum hV hV0 f
  have hfinal : Filter.Tendsto (fun _ : ℕ => ‖f‖ ^ 2) Filter.atTop
      (nhds (‖historyLimit V f‖ ^ 2 + ∑' k, ‖historyResidual V f k‖ ^ 2)) := by
    have h := hstage.add hsum
    simpa [← heq] using h
  exact tendsto_nhds_unique hconst hfinal

omit [CompleteSpace E] in
theorem historyStage_add (f g : E) (n : ℕ) :
    historyStage V (f + g) n = historyStage V f n + historyStage V g n :=
  map_add _ _ _

omit [CompleteSpace E] in
theorem historyStage_smul (c : 𝕜) (f : E) (n : ℕ) :
    historyStage V (c • f) n = c • historyStage V f n :=
  map_smul _ _ _

omit [CompleteSpace E] in
theorem historyResidual_add (f g : E) (k : ℕ) :
    historyResidual V (f + g) k = historyResidual V f k + historyResidual V g k := by
  simp only [historyResidual, historyStage_add]
  abel

omit [CompleteSpace E] in
theorem historyResidual_smul (c : 𝕜) (f : E) (k : ℕ) :
    historyResidual V (c • f) k = c • historyResidual V f k := by
  simp only [historyResidual, historyStage_smul, smul_sub]

theorem historyLimit_add (hV : Antitone V) (hV0 : V 0 = ⊤) (f g : E) :
    historyLimit V (f + g) = historyLimit V f + historyLimit V g := by
  refine tendsto_nhds_unique (tendsto_historyStage hV hV0 (f + g)) ?_
  simpa [historyStage_add] using
    (tendsto_historyStage hV hV0 f).add (tendsto_historyStage hV hV0 g)

theorem historyLimit_smul (hV : Antitone V) (hV0 : V 0 = ⊤) (c : 𝕜) (f : E) :
    historyLimit V (c • f) = c • historyLimit V f := by
  refine tendsto_nhds_unique (tendsto_historyStage hV hV0 (c • f)) ?_
  simpa [historyStage_smul] using (tendsto_historyStage hV hV0 f).const_smul c

omit [CompleteSpace E] in
theorem memℓp_historyResidual (hV : Antitone V) (hV0 : V 0 = ⊤) (f : E) :
    Memℓp (fun k => historyResidual V f k) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  have h : ∀ k, ‖historyResidual V f k‖ ^ (2 : ℝ≥0∞).toReal
      = ‖historyResidual V f k‖ ^ 2 := by
    intro k
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simpa [h] using summable_norm_sq_residual hV hV0 f

variable (V)

/-- `(PMP.25)`  The vertical currents of an infinite history as an `ℓ²` vector. -/
def historyResidualLp (hV : Antitone V) (hV0 : V 0 = ⊤) (f : E) : lp (fun _ : ℕ => E) 2 :=
  ⟨fun k => historyResidual V f k, memℓp_historyResidual hV hV0 f⟩

variable {V}

omit [CompleteSpace E] in
theorem norm_sq_historyResidualLp (hV : Antitone V) (hV0 : V 0 = ⊤) (f : E) :
    ‖historyResidualLp V hV hV0 f‖ ^ 2 = ∑' k, ‖historyResidual V f k‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ => E)
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (historyResidualLp V hV hV0 f)
  rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num] at h
  simpa [Real.rpow_natCast, historyResidualLp] using h

/-- `(PMP.25)`, `(PMP.26)`  The infinite analysis map. -/
def historyAnalysisInf (hV : Antitone V) (hV0 : V 0 = ⊤) :
    E →ₗᵢ[𝕜] WithLp 2 (E × lp (fun _ : ℕ => E) 2) where
  toFun f := WithLp.toLp 2 (historyLimit V f, historyResidualLp V hV hV0 f)
  map_add' f g := by
    have h1 : historyLimit V (f + g) = historyLimit V f + historyLimit V g :=
      historyLimit_add hV hV0 f g
    have h2 : historyResidualLp V hV hV0 (f + g)
        = historyResidualLp V hV hV0 f + historyResidualLp V hV hV0 g :=
      Subtype.ext (funext fun k => historyResidual_add f g k)
    rw [h1, h2]
    rfl
  map_smul' c f := by
    have h1 : historyLimit V (c • f) = c • historyLimit V f := historyLimit_smul hV hV0 c f
    have h2 : historyResidualLp V hV hV0 (c • f) = c • historyResidualLp V hV hV0 f :=
      Subtype.ext (funext fun k => historyResidual_smul c f k)
    rw [h1, h2]
    rfl
  norm_map' f := by
    have hsq : ‖WithLp.toLp 2 (historyLimit V f, historyResidualLp V hV hV0 f)‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd,
        norm_sq_historyResidualLp hV hV0 f, ← norm_sq_eq_historyLimit_add_tsum hV hV0 f]
    have h1 : 0 ≤ ‖WithLp.toLp 2 (historyLimit V f, historyResidualLp V hV hV0 f)‖ := norm_nonneg _
    have h2 := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq h1, Real.sqrt_sq (norm_nonneg f)] at h2

end

end GaloisForLFunctions.HTGeometry
