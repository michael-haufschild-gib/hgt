import GaloisForLFunctions.HTGeometry.ObserverInvisibleTubeShortcut
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity
import GaloisForLFunctions.HTGeometry.ExactPenaltyCircuitBellman
import GaloisForLFunctions.HTGeometry.CommutingPauliObserverRankDominance

/-!
# A fast-forwardable stratum caps every uniform no-shortcut exponent

If a linear subspace of coefficient directions carries a bounded synthesis certificate, then the
Duhamel bound makes the whole tube of radius `r/t` around its `t`-dilate carry the same bounded
certificate at slack `ε₊`.  A standard Gaussian charges that tube with at least a fixed constant
times `t^{-d}`, where `d` is the codimension of the stratum.  Hence no uniform upper no-shortcut
law `K t^{-κ}` can have `κ` larger than the codimension.

The Gaussian shell factor is positive, so the bound is not vacuous.
-/

open MeasureTheory ProbabilityTheory Metric Set Matrix
open scoped BigOperators Matrix Matrix.Norms.L2Operator NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

noncomputable section

/-! ## Bounded synthesis certificates -/

variable {X : Type*} [MetricSpace X] {Γ : Type*}

/-- A finite word within slack `eps` certifies its length as an upper bound on approximate
complexity. -/
theorem approxComplexity_le_of_witness (act : Γ → X → X) (chi : X) {eps : ℝ} {x : X} {B : ℕ}
    (w : List Γ) (hw : w.length ≤ B) (hd : dist x (wordAct act w chi) ≤ eps) :
    approxComplexity act chi eps x ≤ B :=
  Nat.sInf_le ⟨w, hw, hd⟩

/-- Enlarging the slack by the distance moved keeps a certificate valid. -/
theorem exists_witness_of_dist_le {act : Γ → X → X} {chi : X} {eps delta : ℝ} {x y : X} {B : ℕ}
    (hxy : dist x y ≤ delta)
    (hy : ∃ w : List Γ, w.length ≤ B ∧ dist y (wordAct act w chi) ≤ eps) :
    ∃ w : List Γ, w.length ≤ B ∧ dist x (wordAct act w chi) ≤ eps + delta := by
  obtain ⟨w, hw, hd⟩ := hy
  exact ⟨w, hw, le_trans (dist_triangle x y (wordAct act w chi)) (by linarith)⟩

/-! ## The dilated orbit of a coefficient vector -/

section Orbit

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Endpoint of the autonomous orbit of a coefficient vector at time `t`. -/
def orbitState (H : Matrix d d ℂ) (ψ : EuclideanSpace ℂ d) (t : ℝ) : EuclideanSpace ℂ d :=
  (EuclideanSpace.equiv d ℂ).symm (unitaryEvolution H t *ᵥ ψ.ofLp)

theorem dist_orbitState_le {H K : Matrix d d ℂ} (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K)
    (ψ : EuclideanSpace ℂ d) (hψ : ‖ψ‖ = 1) (t : ℝ) :
    dist (orbitState H ψ t) (orbitState K ψ t) ≤ |t| * ‖H - K‖ := by
  have h := QuantumAlg.norm_unitaryEvolution_mulVec_sub_le hH hK t ψ
  rw [hψ, mul_one] at h
  simpa [orbitState, dist_eq_norm] using h

end Orbit

/-! ## The fast-forwardable tube -/

section Tube

variable {d : Type*} [Fintype d] [DecidableEq d] {Γ : Type*} {f v : ℕ}

/-- **Tube inclusion.**  Every coefficient vector whose transverse part has norm at most `r/t`
inherits, at slack `ε₊`, the bounded synthesis certificate of the stratum. -/
theorem exists_witness_tube
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    (Hmap : ((Fin f → ℝ) × (Fin v → ℝ)) →ₗ[ℝ] Matrix d d ℂ)
    (hherm : ∀ w, IsSelfAdjoint (Hmap w))
    {L : ℝ} (hL : 0 < L)
    (hlip : ∀ u w, ‖Hmap u - Hmap w‖ ≤ L * ‖u - w‖)
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    {epsMinus epsPlus r : ℝ} {B : ℕ}
    (hstratum : ∀ (y : Fin f → ℝ) (s : ℝ), ∃ w : List Γ, w.length ≤ B ∧
      dist (orbitState (Hmap (y, 0)) ψ s) (wordAct act w chi) ≤ epsMinus)
    (hgap : L * r ≤ epsPlus - epsMinus)
    {t : ℝ} (ht : 0 < t) {p : (Fin f → ℝ) × (Fin v → ℝ)} (hp : ‖p.2‖ ≤ r / t) :
    approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B := by
  have hdiff : ‖Hmap p - Hmap (p.1, 0)‖ ≤ L * ‖p.2‖ := by
    refine le_trans (hlip p (p.1, 0)) ?_
    have hsub : p - (p.1, 0) = (0, p.2) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [hsub]
    have : ‖((0 : Fin f → ℝ), p.2)‖ = ‖p.2‖ := by simp [Prod.norm_def]
    rw [this]
  have hmove : dist (orbitState (Hmap p) ψ t) (orbitState (Hmap (p.1, 0)) ψ t) ≤
      epsPlus - epsMinus := by
    refine le_trans (dist_orbitState_le (hherm p) (hherm (p.1, 0)) ψ hψ t) ?_
    have hstep : |t| * ‖Hmap p - Hmap (p.1, 0)‖ ≤ t * (L * (r / t)) := by
      rw [abs_of_pos ht]
      exact mul_le_mul_of_nonneg_left
        (le_trans hdiff (mul_le_mul_of_nonneg_left hp hL.le)) ht.le
    have hval : t * (L * (r / t)) = L * r := by field_simp
    rw [hval] at hstep
    linarith
  obtain ⟨w, hw, hd⟩ :=
    exists_witness_of_dist_le (act := act) (chi := chi) hmove (hstratum p.1 t)
  refine approxComplexity_le_of_witness act chi w hw ?_
  linarith

omit [Fintype d] [DecidableEq d] in
/-- **Cost admissibility.**  On the shell `‖p₁‖ ≥ 1`, after the stated pre-capacity time the
bounded certificate is below the allowed cost budget. -/
theorem le_cost_budget
    (Hmap : ((Fin f → ℝ) × (Fin v → ℝ)) →ₗ[ℝ] Matrix d d ℂ)
    (Lam : Matrix d d ℂ → ℝ) {lamMinus : ℝ} (hlam : 0 < lamMinus)
    (hLam : ∀ x, lamMinus * ‖x‖ ≤ Lam (Hmap x))
    {a pn : ℝ} (ha : 0 < a) (hpn : 0 < pn) {B : ℕ}
    {t : ℝ} (ht : 2 * B * pn / (a * lamMinus) ≤ t) (ht0 : 0 < t)
    {p : (Fin f → ℝ) × (Fin v → ℝ)} (hp : 1 ≤ ‖p.1‖) :
    (B : ℝ) ≤ a * Lam (Hmap (t • p)) / pn := by
  have hnorm : ‖p.1‖ ≤ ‖p‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  have hscale : ‖t • p‖ = t * ‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  have hge : lamMinus * t ≤ Lam (Hmap (t • p)) := by
    refine le_trans ?_ (hLam (t • p))
    rw [hscale]
    have h1 : (1 : ℝ) ≤ ‖p‖ := le_trans hp hnorm
    have : t ≤ t * ‖p‖ := by nlinarith [ht0]
    nlinarith [hlam.le, this]
  have hB : 2 * (B : ℝ) * pn ≤ a * lamMinus * t := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < a * lamMinus)).mp ht
    linarith
  have hBnn : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  rw [le_div_iff₀ hpn]
  nlinarith [hge, ha, hlam, ht0]

end Tube


/-! ## Deterministic radial tube volume -/

section Radial

variable {d : Type*} [Fintype d] [DecidableEq d] {Γ : Type*} {f v : ℕ}

/-- **Radial shortcut locus.**  At unit time the shortcut locus contains the fixed-radius tube
around the stratum, so its Haar measure over the shell `R ≤ ‖p₁‖ ≤ 2R` grows like `R ^ f`. -/
theorem measure_shortcutLocus_ge_annulusTube
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    (Hmap : ((Fin f → ℝ) × (Fin v → ℝ)) →ₗ[ℝ] Matrix d d ℂ)
    (hherm : ∀ w, IsSelfAdjoint (Hmap w))
    {L : ℝ} (hL : 0 < L)
    (hlip : ∀ u w, ‖Hmap u - Hmap w‖ ≤ L * ‖u - w‖)
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    {epsMinus epsPlus r : ℝ} {B : ℕ}
    (hstratum : ∀ (y : Fin f → ℝ) (s : ℝ), ∃ w : List Γ, w.length ≤ B ∧
      dist (orbitState (Hmap (y, 0)) ψ s) (wordAct act w chi) ≤ epsMinus)
    (hr : 0 ≤ r) (hgap : L * r ≤ epsPlus - epsMinus)
    (μ : Measure (Fin f → ℝ)) [μ.IsAddHaarMeasure]
    (ν : Measure (Fin v → ℝ)) [ν.IsAddHaarMeasure] [SFinite ν]
    {R : ℝ} (hR : 0 ≤ R) :
    ENNReal.ofReal ((2 ^ f - 1) * R ^ f) * μ (ball 0 1) *
        (ENNReal.ofReal (r ^ v) * ν (ball 0 1))
      ≤ (μ.prod ν) {p : (Fin f → ℝ) × (Fin v → ℝ) |
          approxComplexity act chi epsPlus (orbitState (Hmap p) ψ 1) ≤ B} := by
  have hrank : ∀ k : ℕ, Module.finrank ℝ (Fin k → ℝ) = k := fun k => Module.finrank_fin_fun ℝ
  have heq := measure_annulusTube (E := Fin f → ℝ) (F := Fin v → ℝ) μ ν hR hr
  rw [hrank f, hrank v] at heq
  rw [← heq]
  refine measure_mono ?_
  rintro ⟨x, y⟩ ⟨-, hy⟩
  have hynorm : ‖y‖ ≤ r / 1 := by simpa using hy
  exact exists_witness_tube hψ Hmap hherm hL hlip act chi hstratum hgap one_pos hynorm

end Radial

/-! ## The commuting Pauli sector -/

/-- Dimension of the commuting `Z`-string sector of the fixed-weight Pauli coefficient space. -/
def zStringSectorDim (n q : ℕ) : ℕ := ∑ j ∈ Finset.range q, n.choose (j + 1)

theorem zStringSectorDim_le_nonidentityPauliWeightCount (n q : ℕ) :
    zStringSectorDim n q ≤ Quantum.nonidentityPauliWeightCount n q := by
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : (1 : ℕ) ≤ 3 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
  calc n.choose (j + 1) = 1 * n.choose (j + 1) := (one_mul _).symm
    _ ≤ 3 ^ (j + 1) * n.choose (j + 1) := Nat.mul_le_mul_right _ h1

/-- The Pauli codimension of the commuting `Z`-string sector. -/
theorem nonidentityPauliWeightCount_sub_zStringSectorDim (n q : ℕ) :
    Quantum.nonidentityPauliWeightCount n q - zStringSectorDim n q =
      ∑ j ∈ Finset.range q, (3 ^ (j + 1) - 1) * n.choose (j + 1) := by
  unfold Quantum.nonidentityPauliWeightCount zStringSectorDim
  rw [← Finset.sum_tsub_distrib]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.sub_mul, one_mul]
  · intro j _
    have h1 : (1 : ℕ) ≤ 3 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
    calc n.choose (j + 1) = 1 * n.choose (j + 1) := (one_mul _).symm
      _ ≤ 3 ^ (j + 1) * n.choose (j + 1) := Nat.mul_le_mul_right _ h1

/-! ## The Gaussian codimension bound -/

section Gaussian

variable {d : Type*} [Fintype d] [DecidableEq d] {Γ : Type*} {f v : ℕ}

/-- **Fast-forwardable stratum shortcut mass.**  A standard Gaussian charges the set of
coefficient vectors admitting the bounded certificate with at least a fixed positive constant
times `t^{-v}`, where `v` is the codimension of the stratum. -/
theorem measure_shortcut_ge
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    (Hmap : ((Fin f → ℝ) × (Fin v → ℝ)) →ₗ[ℝ] Matrix d d ℂ)
    (hherm : ∀ w, IsSelfAdjoint (Hmap w))
    {L : ℝ} (hL : 0 < L)
    (hlip : ∀ u w, ‖Hmap u - Hmap w‖ ≤ L * ‖u - w‖)
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    (Lam : Matrix d d ℂ → ℝ) {lamMinus : ℝ} (hlam : 0 < lamMinus)
    (hLam : ∀ x, lamMinus * ‖x‖ ≤ Lam (Hmap x))
    {epsMinus epsPlus r a pn : ℝ} {B : ℕ}
    (hstratum : ∀ (y : Fin f → ℝ) (s : ℝ), ∃ w : List Γ, w.length ≤ B ∧
      dist (orbitState (Hmap (y, 0)) ψ s) (wordAct act w chi) ≤ epsMinus)
    (hr : 0 < r) (hgap : L * r ≤ epsPlus - epsMinus)
    (ha : 0 < a) (hpn : 0 < pn)
    {t : ℝ} (ht0 : 0 < t) (htr : r ≤ t) (htB : 2 * B * pn / (a * lamMinus) ≤ t) :
    (Measure.pi fun _ : Fin f => gaussianReal 0 1)
          {x : Fin f → ℝ | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} *
        ENNReal.ofReal ((2 * gaussianDensityFloor * r) ^ v * (t ^ v)⁻¹)
      ≤ ((Measure.pi fun _ : Fin f => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin v => gaussianReal 0 1))
          {p : (Fin f → ℝ) × (Fin v → ℝ) |
            approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B ∧
              (B : ℝ) ≤ a * Lam (Hmap (t • p)) / pn} := by
  have hsub : ({x : Fin f → ℝ | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ×ˢ closedBall (0 : Fin v → ℝ) (r / t)) ⊆
      {p : (Fin f → ℝ) × (Fin v → ℝ) |
        approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B ∧
          (B : ℝ) ≤ a * Lam (Hmap (t • p)) / pn} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hynorm : ‖y‖ ≤ r / t := by simpa using hy
    refine ⟨?_, ?_⟩
    · exact exists_witness_tube hψ Hmap hherm hL hlip act chi hstratum hgap ht0 hynorm
    · exact le_cost_budget Hmap Lam hlam hLam ha hpn htB ht0 hx.1
  refine le_trans ?_ (measure_mono hsub)
  rw [Measure.prod_prod]
  gcongr
  have hLt : L * r ≤ L * t := mul_le_mul_of_nonneg_left htr hL.le
  have hball := measure_pi_gaussian_transverse_ball_lower (L := L) (ε := L * r) v hL
    (by positivity) ht0 hLt
  have hradius : L * r / (L * t) = r / t := by field_simp
  rw [hradius] at hball
  have hconst : L * r / L = r := by field_simp
  rw [hconst] at hball
  exact hball

/-- **Codimension ceiling.**  A uniform upper no-shortcut law `K t^{-κ}` cannot beat the
fast-forwardable tube, so its exponent is at most the codimension of the stratum. -/
theorem exponent_le_codimension
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1)
    (Hmap : ((Fin f → ℝ) × (Fin v → ℝ)) →ₗ[ℝ] Matrix d d ℂ)
    (hherm : ∀ w, IsSelfAdjoint (Hmap w))
    {L : ℝ} (hL : 0 < L)
    (hlip : ∀ u w, ‖Hmap u - Hmap w‖ ≤ L * ‖u - w‖)
    (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d) (chi : EuclideanSpace ℂ d)
    (Lam : Matrix d d ℂ → ℝ) {lamMinus : ℝ} (hlam : 0 < lamMinus)
    (hLam : ∀ x, lamMinus * ‖x‖ ≤ Lam (Hmap x))
    {epsMinus epsPlus r a pn : ℝ} {B : ℕ}
    (hstratum : ∀ (y : Fin f → ℝ) (s : ℝ), ∃ w : List Γ, w.length ≤ B ∧
      dist (orbitState (Hmap (y, 0)) ψ s) (wordAct act w chi) ≤ epsMinus)
    (hr : 0 < r) (hgap : L * r ≤ epsPlus - epsMinus)
    (ha : 0 < a) (hpn : 0 < pn) (hf : 0 < f)
    {K κ T : ℝ}
    (hupper : ∀ t : ℝ, T ≤ t → 1 ≤ t →
      (((Measure.pi fun _ : Fin f => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin v => gaussianReal 0 1))
        {p : (Fin f → ℝ) × (Fin v → ℝ) |
          approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B ∧
            (B : ℝ) ≤ a * Lam (Hmap (t • p)) / pn}).toReal ≤ K * t ^ (-κ)) :
    κ ≤ (v : ℝ) := by
  classical
  set pf : ℝ≥0∞ := (Measure.pi fun _ : Fin f => gaussianReal 0 1)
    {x : Fin f → ℝ | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} with hpf
  have hpfpos : 0 < pf := measure_pi_gaussian_shell_pos hf
  have hpftop : pf ≠ ⊤ := measure_ne_top _ _
  have hpfreal : 0 < pf.toReal := ENNReal.toReal_pos hpfpos.ne' hpftop
  have hbase : 0 < 2 * gaussianDensityFloor * r :=
    mul_pos (by linarith [gaussianDensityFloor_pos]) hr
  refine exponent_le_natCast_of_forall_le
    (c := (2 * gaussianDensityFloor * r) ^ v * pf.toReal) (K := K)
    (T := max (max T r) (2 * B * pn / (a * lamMinus)))
    (by positivity) ?_
  intro t htT ht1
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have htr : r ≤ t := le_trans (le_trans (le_max_right T r) (le_max_left _ _)) htT
  have htB : 2 * B * pn / (a * lamMinus) ≤ t := le_trans (le_max_right _ _) htT
  have htT' : T ≤ t := le_trans (le_trans (le_max_left T r) (le_max_left _ _)) htT
  have hmeas := measure_shortcut_ge hψ Hmap hherm hL hlip act chi Lam hlam hLam
    hstratum hr hgap ha hpn ht0 htr htB
  have hupperT := hupper t htT' ht1
  have hfin : (((Measure.pi fun _ : Fin f => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin v => gaussianReal 0 1))
      {p : (Fin f → ℝ) × (Fin v → ℝ) |
        approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B ∧
          (B : ℝ) ≤ a * Lam (Hmap (t • p)) / pn}) ≠ ⊤ := measure_ne_top _ _
  have hlhs : ((2 * gaussianDensityFloor * r) ^ v * pf.toReal) * (t ^ v)⁻¹ ≤
      (((Measure.pi fun _ : Fin f => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin v => gaussianReal 0 1))
        {p : (Fin f → ℝ) × (Fin v → ℝ) |
          approxComplexity act chi epsPlus (orbitState (Hmap p) ψ t) ≤ B ∧
            (B : ℝ) ≤ a * Lam (Hmap (t • p)) / pn}).toReal := by
    have hstep := ENNReal.toReal_mono hfin hmeas
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hstep
    calc ((2 * gaussianDensityFloor * r) ^ v * pf.toReal) * (t ^ v)⁻¹
        = pf.toReal * ((2 * gaussianDensityFloor * r) ^ v * (t ^ v)⁻¹) := by ring
      _ ≤ _ := hstep
  linarith

end Gaussian

end

end GaloisForLFunctions.HTGeometry
