import Mathlib

/-!
# The cross-observer lifting modulus

How much separation one realization can hide inside a small ball of another is measured by the
lifting modulus.  Its zero-scale value decides exact factorization; its behaviour at small positive
scale decides uniform (conditioned) factorization.  A fixed finite observer has a resolution floor,
so the modulus is locally constant there; a linear observer has modulus `ε/σ_min`; and a cofinal
family can have infinite horizon even when every member is injective.
-/

open Filter Topology

open scoped ENNReal NNReal

namespace HTGeometry.ConstraintRelativity

/-! ## An extended-real helper -/

theorem eq_top_of_forall_ofReal_le {a : ℝ≥0∞} (h : ∀ M : ℝ, 0 ≤ M → ENNReal.ofReal M ≤ a) :
    a = ⊤ := by
  by_contra hcon
  have hnn : (0 : ℝ) ≤ a.toReal := ENNReal.toReal_nonneg
  have h1 := h (a.toReal + 1) (by linarith)
  rw [ENNReal.ofReal_le_iff_le_toReal hcon] at h1
  linarith

/-! ## Definition -/

section Definition

variable {S B I : Type*} [PseudoMetricSpace B] [PseudoMetricSpace I]

/-- **Card `(1)`.**  The cross-observer lifting modulus. -/
noncomputable def liftingModulus (p : S → I) (q : S → B) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ (x : S) (y : S) (_ : dist (q x) (q y) ≤ ε), ENNReal.ofReal (dist (p x) (p y))

theorem le_liftingModulus (p : S → I) (q : S → B) {ε : ℝ} {x y : S}
    (h : dist (q x) (q y) ≤ ε) : ENNReal.ofReal (dist (p x) (p y)) ≤ liftingModulus p q ε := by
  simp only [liftingModulus]
  exact le_iSup_of_le x (le_iSup_of_le y (le_iSup_of_le h le_rfl))

theorem liftingModulus_le (p : S → I) (q : S → B) {ε : ℝ} {c : ℝ≥0∞}
    (h : ∀ x y : S, dist (q x) (q y) ≤ ε → ENNReal.ofReal (dist (p x) (p y)) ≤ c) :
    liftingModulus p q ε ≤ c :=
  iSup_le fun a => iSup_le fun b => iSup_le fun hab => h a b hab

/-- The modulus is monotone in the scale. -/
theorem liftingModulus_mono (p : S → I) (q : S → B) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    liftingModulus p q ε₁ ≤ liftingModulus p q ε₂ :=
  liftingModulus_le p q fun _ _ hxy => le_liftingModulus p q (hxy.trans h)

/-- **Card `(4)`.**  Every pair is controlled by the modulus at its own observed separation. -/
theorem dist_le_liftingModulus (p : S → I) (q : S → B) (x y : S) :
    ENNReal.ofReal (dist (p x) (p y)) ≤ liftingModulus p q (dist (q x) (q y)) :=
  le_liftingModulus p q le_rfl

end Definition

/-! ## Zero scale is exact factorization -/

section ZeroScale

variable {S B I : Type*} [MetricSpace B] [MetricSpace I]

/-- **Card `(2)`.**  The zero-scale modulus vanishes exactly when the second observer is constant
on the fibres of the first. -/
theorem liftingModulus_zero_eq_zero_iff (p : S → I) (q : S → B) :
    liftingModulus p q 0 = 0 ↔ ∀ x y : S, q x = q y → p x = p y := by
  constructor
  · intro h x y hxy
    have hd : dist (q x) (q y) ≤ 0 := by rw [hxy, dist_self]
    have := le_liftingModulus p q hd
    rw [h, le_zero_iff, ENNReal.ofReal_eq_zero] at this
    exact dist_le_zero.1 this
  · intro h
    refine le_antisymm (liftingModulus_le p q fun x y hxy => ?_) bot_le
    have hq : q x = q y := by
      have : dist (q x) (q y) = 0 := le_antisymm hxy dist_nonneg
      exact dist_eq_zero.1 this
    rw [h x y hq, dist_self, ENNReal.ofReal_zero]

/-- **Card `(3)`.**  For a compact source with continuous observers, exactness at scale zero forces
the modulus to be small at some positive scale.  Without compactness the modulus can jump at zero:
this is where the card's compactness assumption is used. -/
theorem exists_liftingModulus_le_of_zero {S : Type*} [MetricSpace S] [CompactSpace S]
    {p : S → I} {q : S → B} (hp : Continuous p) (hq : Continuous q)
    (h0 : liftingModulus p q 0 = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > (0 : ℝ), liftingModulus p q ε ≤ ENNReal.ofReal δ := by
  classical
  by_contra hcon
  have hbig : ∀ n : ℕ, ∃ x y : S,
      dist (q x) (q y) ≤ 1 / ((n : ℝ) + 1) ∧ δ < dist (p x) (p y) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hnot : ¬ liftingModulus p q (1 / ((n : ℝ) + 1)) ≤ ENNReal.ofReal δ := fun h =>
      hcon ⟨1 / ((n : ℝ) + 1), hpos, h⟩
    rw [not_le] at hnot
    simp only [liftingModulus, lt_iSup_iff] at hnot
    obtain ⟨x, y, hxy, hlt⟩ := hnot
    exact ⟨x, y, hxy, by rwa [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ.le] at hlt⟩
  choose X Y hQ hP using hbig
  obtain ⟨x₀, -, φ, hφ, hx⟩ :=
    (isCompact_univ (X := S)).tendsto_subseq (x := X) fun n => Set.mem_univ (X n)
  obtain ⟨y₀, -, ψ, hψ, hy⟩ :=
    (isCompact_univ (X := S)).tendsto_subseq (x := fun n => Y (φ n)) fun n => Set.mem_univ _
  set χ : ℕ → ℕ := fun n => φ (ψ n) with hχ
  have hXχ : Filter.Tendsto (fun n => X (χ n)) Filter.atTop (nhds x₀) :=
    hx.comp hψ.tendsto_atTop
  have hYχ : Filter.Tendsto (fun n => Y (χ n)) Filter.atTop (nhds y₀) := hy
  have hqlim : Filter.Tendsto (fun n => dist (q (X (χ n))) (q (Y (χ n)))) Filter.atTop
      (nhds (dist (q x₀) (q y₀))) :=
    ((hq.tendsto x₀).comp hXχ).dist ((hq.tendsto y₀).comp hYχ)
  have hsmall : Filter.Tendsto (fun n => 1 / ((χ n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_natCast_atTop_atTop.comp (hφ.comp hψ).tendsto_atTop)
  have hqzero : dist (q x₀) (q y₀) ≤ 0 :=
    le_of_tendsto_of_tendsto' hqlim hsmall fun n => hQ (χ n)
  have hqeq : q x₀ = q y₀ := dist_le_zero.1 hqzero
  have hpeq : p x₀ = p y₀ := (liftingModulus_zero_eq_zero_iff p q).1 h0 x₀ y₀ hqeq
  have hplim : Filter.Tendsto (fun n => dist (p (X (χ n))) (p (Y (χ n)))) Filter.atTop
      (nhds (dist (p x₀) (p y₀))) :=
    ((hp.tendsto x₀).comp hXχ).dist ((hp.tendsto y₀).comp hYχ)
  have hδle : δ ≤ dist (p x₀) (p y₀) :=
    ge_of_tendsto' hplim fun n => (hP (χ n)).le
  rw [hpeq, dist_self] at hδle
  exact absurd hδle (not_le.2 hδ)

/-- **Card `(3)`.**  Equivalently: for a compact source with continuous observers, the observer
factors continuously exactly when the modulus tends to zero with the scale. -/
theorem tendsto_liftingModulus_nhdsGT_zero_iff {S : Type*} [MetricSpace S] [CompactSpace S]
    {p : S → I} {q : S → B} (hp : Continuous p) (hq : Continuous q) :
    liftingModulus p q 0 = 0 ↔
      Filter.Tendsto (liftingModulus p q) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  constructor
  · intro h0
    rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    rcases eq_or_ne η ⊤ with rfl | hηtop
    · exact Filter.Eventually.of_forall fun _ => le_top
    · have hpos : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
      obtain ⟨ε, hε, hle⟩ := exists_liftingModulus_le_of_zero hp hq h0 hpos
      rw [ENNReal.ofReal_toReal hηtop] at hle
      filter_upwards [Ioo_mem_nhdsGT hε] with t ht
      exact le_trans (liftingModulus_mono p q ht.2.le) hle
  · intro hlim
    refine le_antisymm ?_ bot_le
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact liftingModulus_mono p q (le_of_lt ht)

/-- **Card `(2)`.**  In that case the factoring map exists on the image. -/
noncomputable def liftFactor (p : S → I) (q : S → B) [Nonempty I]
    (_h : ∀ x y : S, q x = q y → p x = p y) : B → I := by
  classical
  exact fun b => if hb : ∃ x : S, q x = b then p hb.choose else Classical.arbitrary I

omit [MetricSpace B] [MetricSpace I] in
theorem liftFactor_comp (p : S → I) (q : S → B) [Nonempty I]
    (h : ∀ x y : S, q x = q y → p x = p y) (x : S) : liftFactor p q h (q x) = p x := by
  classical
  have hb : ∃ y : S, q y = q x := ⟨x, rfl⟩
  rw [liftFactor, dif_pos hb]
  exact h _ _ hb.choose_spec

/-- **Card `(18)`.**  A Lipschitz decoder bounds every source separation by the observed one. -/
theorem dist_le_of_lipschitz_factor {p : S → I} {q : S → B} {r : B → I} {K : NNReal}
    (hr : LipschitzWith K r) (hfact : ∀ x, p x = r (q x)) (x y : S) :
    dist (p x) (p y) ≤ K * dist (q x) (q y) := by
  rw [hfact x, hfact y]
  exact hr.dist_le_mul _ _

end ZeroScale

/-! ## Composition and coarsening -/

section Composition

variable {S B I C : Type*} [PseudoMetricSpace B] [PseudoMetricSpace I] [PseudoMetricSpace C]

/-- **Card `(5)`.**  The modulus composes. -/
theorem liftingModulus_comp (r : S → C) (p : S → I) (q : S → B) (ε δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : liftingModulus p q ε ≤ ENNReal.ofReal δ) :
    liftingModulus r q ε ≤ liftingModulus r p δ := by
  refine liftingModulus_le r q fun x y hxy => ?_
  refine le_liftingModulus r p ?_
  have h1 : ENNReal.ofReal (dist (p x) (p y)) ≤ ENNReal.ofReal δ :=
    le_trans (le_liftingModulus p q hxy) hδ
  exact (ENNReal.ofReal_le_ofReal_iff hδ0).1 h1

/-- **Card `(6)`.**  Coarsening the first observer by a `1`-Lipschitz map can only increase the
modulus. -/
theorem liftingModulus_le_of_lipschitz {B' : Type*} [PseudoMetricSpace B'] (p : S → I) (q : S → B)
    (f : B → B') (hf : LipschitzWith 1 f) (ε : ℝ) :
    liftingModulus p q ε ≤ liftingModulus p (f ∘ q) ε := by
  refine liftingModulus_le p q fun x y hxy => ?_
  refine le_liftingModulus p (f ∘ q) ?_
  calc dist (f (q x)) (f (q y)) ≤ (1 : NNReal) * dist (q x) (q y) := hf.dist_le_mul _ _
    _ = dist (q x) (q y) := by simp
    _ ≤ ε := hxy

end Composition

/-! ## The resolution floor of a finite exact observer -/

section Floor

variable {S B I : Type*} [PseudoMetricSpace B] [PseudoMetricSpace I]

/-- **Card `(7)`, `(8)`.**  Below the separation of a finite observer the modulus is constant. -/
theorem liftingModulus_eq_zero_scale (p : S → I) (q : S → B) {σ : ℝ}
    (hσ : ∀ x y : S, q x ≠ q y → σ ≤ dist (q x) (q y)) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < σ) :
    liftingModulus p q ε = liftingModulus p q 0 := by
  refine le_antisymm (liftingModulus_le p q fun x y hxy => ?_) (liftingModulus_mono p q hε0)
  refine le_liftingModulus p q ?_
  by_cases hq : q x = q y
  · rw [hq, dist_self]
  · exact absurd (le_trans (hσ x y hq) hxy) (not_le.2 hε)

end Floor

/-! ## The linear deformation-descent condition number -/

section Linear

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B]
  [NormedSpace ℝ B]

/-- **Card `(9)`.**  A nonzero kernel makes the modulus infinite at every scale. -/
theorem liftingModulus_eq_top_of_ker (J : E →L[ℝ] B) {v : E} (hv : v ≠ 0) (hJv : J v = 0)
    {ε : ℝ} (hε : 0 ≤ ε) : liftingModulus (id : E → E) J ε = ⊤ := by
  refine eq_top_of_forall_ofReal_le fun M hM => ?_
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.2 hv
  set t : ℝ := M / ‖v‖ with ht
  have hpair : dist (J (t • v)) (J 0) ≤ ε := by
    simp [hJv, hε]
  have hle := le_liftingModulus (id : E → E) J hpair
  have hnorm : dist (id (t • v)) (id (0 : E)) = M := by
    rw [id, id, dist_zero_right, norm_smul, Real.norm_eq_abs, ht, abs_div,
      abs_of_nonneg hM, abs_of_pos hvn, div_mul_cancel₀ _ hvn.ne']
  rwa [hnorm] at hle

variable [Nontrivial E]

instance sphereNonemptyOfNontrivial : Nonempty (Metric.sphere (0 : E) 1) :=
  (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype

/-- The least singular value of a linear observer. -/
noncomputable def sigmaMin (J : E →L[ℝ] B) : ℝ := ⨅ v : Metric.sphere (0 : E) 1, ‖J v‖

theorem sigmaMin_nonneg (J : E →L[ℝ] B) : 0 ≤ sigmaMin J :=
  le_ciInf fun _ => norm_nonneg _

omit [Nontrivial E] in
theorem sigmaMin_le_of_norm_one (J : E →L[ℝ] B) {v : E} (hv : ‖v‖ = 1) :
    sigmaMin J ≤ ‖J v‖ :=
  ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨v, by simpa using hv⟩ :
    Metric.sphere (0 : E) 1)

omit [Nontrivial E] in
theorem sigmaMin_mul_le (J : E →L[ℝ] B) (v : E) : sigmaMin J * ‖v‖ ≤ ‖J v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.2 hv
    have hunit : ‖(‖v‖)⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hvn, inv_mul_cancel₀ hvn.ne']
    have h := sigmaMin_le_of_norm_one J hunit
    rw [map_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hvn] at h
    rw [← le_div_iff₀ hvn]
    calc sigmaMin J ≤ (‖v‖)⁻¹ * ‖J v‖ := h
      _ = ‖J v‖ / ‖v‖ := by rw [inv_mul_eq_div]

theorem exists_norm_eq_sigmaMin [FiniteDimensional ℝ E] (J : E →L[ℝ] B) :
    ∃ v : E, ‖v‖ = 1 ∧ ‖J v‖ = sigmaMin J := by
  have hne : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  have hcpt : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  obtain ⟨v, hv, hmin⟩ := hcpt.exists_isMinOn hne (J.continuous.norm.continuousOn)
  have hv1 : ‖v‖ = 1 := by simpa using hv
  exact ⟨v, hv1, le_antisymm (le_ciInf fun w => hmin w.2) (sigmaMin_le_of_norm_one J hv1)⟩

/-- **Card `(10)`, boxed.**  For an observer with positive least singular value the modulus is
exactly `ε/σ_min`. -/
theorem liftingModulus_id_linear [FiniteDimensional ℝ E] (J : E →L[ℝ] B)
    (hσ : 0 < sigmaMin J) {ε : ℝ} (hε : 0 ≤ ε) :
    liftingModulus (id : E → E) J ε = ENNReal.ofReal (ε / sigmaMin J) := by
  refine le_antisymm (liftingModulus_le _ _ fun x y hxy => ?_) ?_
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hσ, dist_eq_norm]
    calc ‖x - y‖ * sigmaMin J = sigmaMin J * ‖x - y‖ := by ring
      _ ≤ ‖J (x - y)‖ := sigmaMin_mul_le J _
      _ = dist (J x) (J y) := by rw [map_sub, dist_eq_norm]
      _ ≤ ε := hxy
  · obtain ⟨v, hv, hJv⟩ := exists_norm_eq_sigmaMin J
    have hpair : dist (J ((ε / sigmaMin J) • v)) (J 0) ≤ ε := by
      rw [map_smul, map_zero, dist_zero_right, norm_smul, hJv, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ε / sigmaMin J), div_mul_cancel₀ _ hσ.ne']
    have hle := le_liftingModulus (id : E → E) J hpair
    have hnorm : dist (id ((ε / sigmaMin J) • v)) (id (0 : E)) = ε / sigmaMin J := by
      rw [id, id, dist_zero_right, norm_smul, hv, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ε / sigmaMin J), mul_one]
    rwa [hnorm] at hle

/-- The inverse of an injective map on its range, as a continuous linear map. -/
noncomputable def rangeInverse [FiniteDimensional ℝ E] (J : E →L[ℝ] B)
    (hJ : Function.Injective J) :
    ↥(LinearMap.range (J : E →ₗ[ℝ] B)) →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    ((LinearEquiv.ofInjective (J : E →ₗ[ℝ] B) hJ).symm :
      ↥(LinearMap.range (J : E →ₗ[ℝ] B)) →ₗ[ℝ] E)

omit [Nontrivial E] in
@[simp] theorem apply_rangeInverse [FiniteDimensional ℝ E] (J : E →L[ℝ] B)
    (hJ : Function.Injective J) (w : ↥(LinearMap.range (J : E →ₗ[ℝ] B))) :
    J (rangeInverse J hJ w) = (w : B) := by
  have h := (LinearEquiv.ofInjective (J : E →ₗ[ℝ] B) hJ).apply_symm_apply w
  exact congrArg Subtype.val h

omit [Nontrivial E] in
/-- **Card `(11)`.**  For an injective deformation the lifting modulus of any linear functional is
the scale times the operator norm of the functional composed with the inverse on the range.  This
generalizes the singular-value formula `(10)`, which is the case `ℓ = id`. -/
theorem liftingModulus_linear_functional [FiniteDimensional ℝ E] (J : E →L[ℝ] B)
    (hJ : Function.Injective J) (l : E →L[ℝ] ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    liftingModulus (fun x => l x) (fun x => J x) ε
      = ENNReal.ofReal (ε * ‖l.comp (rangeInverse J hJ)‖) := by
  set T := l.comp (rangeInverse J hJ) with hT
  refine le_antisymm (liftingModulus_le _ _ fun x y hxy => ?_) ?_
  · refine ENNReal.ofReal_le_ofReal ?_
    have hmem : J (x - y) ∈ LinearMap.range (J : E →ₗ[ℝ] B) := ⟨x - y, rfl⟩
    have hinv : rangeInverse J hJ ⟨J (x - y), hmem⟩ = x - y := by
      refine hJ ?_
      rw [apply_rangeInverse]
    have hval : l x - l y = T ⟨J (x - y), hmem⟩ := by
      rw [hT, ContinuousLinearMap.comp_apply, hinv, map_sub]
    have hnorm : ‖(⟨J (x - y), hmem⟩ : ↥(LinearMap.range (J : E →ₗ[ℝ] B)))‖ ≤ ε := by
      show ‖J (x - y)‖ ≤ ε
      rw [map_sub, ← dist_eq_norm]
      exact hxy
    have hop := ContinuousLinearMap.le_opNorm T (⟨J (x - y), hmem⟩ :
      ↥(LinearMap.range (J : E →ₗ[ℝ] B)))
    have hmul : ‖T‖ * ‖(⟨J (x - y), hmem⟩ : ↥(LinearMap.range (J : E →ₗ[ℝ] B)))‖ ≤ ‖T‖ * ε :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg T)
    have hdist : dist (l x) (l y) = ‖T ⟨J (x - y), hmem⟩‖ := by
      rw [Real.dist_eq, ← Real.norm_eq_abs, hval]
    rw [hdist]
    nlinarith [hop, hmul]
  · rcases eq_or_ne (liftingModulus (fun x => l x) (fun x => J x) ε) ⊤ with htop | htop
    · rw [htop]; exact le_top
    refine (ENNReal.ofReal_le_iff_le_toReal htop).2 ?_
    set c := (liftingModulus (fun x => l x) (fun x => J x) ε).toReal with hc
    have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
    have hunit : ∀ w : ↥(LinearMap.range (J : E →ₗ[ℝ] B)), ‖w‖ ≤ 1 → ε * ‖T w‖ ≤ c := by
      intro w hw
      have hwb : ‖(w : B)‖ ≤ 1 := hw
      have hpair : dist (J (rangeInverse J hJ (ε • w))) (J 0) ≤ ε := by
        rw [map_zero, dist_zero_right, apply_rangeInverse]
        show ‖ε • (w : B)‖ ≤ ε
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
        nlinarith [norm_nonneg (w : B)]
      have hle := le_liftingModulus (fun x => l x) (fun x => J x) hpair
      have h1 : l (rangeInverse J hJ (ε • w)) = ε * T w := by
        rw [hT, ContinuousLinearMap.comp_apply, map_smul, map_smul, smul_eq_mul]
      have hval : dist (l (rangeInverse J hJ (ε • w))) (l 0) = ε * ‖T w‖ := by
        rw [h1, map_zero, Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hε, Real.norm_eq_abs]
      rw [hval] at hle
      exact (ENNReal.ofReal_le_iff_le_toReal htop).1 hle
    have hbound : ∀ w : ↥(LinearMap.range (J : E →ₗ[ℝ] B)), ε * ‖T w‖ ≤ c * ‖w‖ := by
      intro w
      rcases eq_or_ne w 0 with rfl | hw0
      · simp
      · have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
        have hinvpos : (0 : ℝ) ≤ ‖w‖⁻¹ := le_of_lt (inv_pos.2 hwpos)
        have hnorm1 : ‖(‖w‖⁻¹ : ℝ) • w‖ ≤ 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinvpos, inv_mul_cancel₀ hwpos.ne']
        have hb := hunit _ hnorm1
        rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinvpos] at hb
        have h2 := mul_le_mul_of_nonneg_right hb hwpos.le
        have heq : (ε * (‖w‖⁻¹ * ‖T w‖)) * ‖w‖ = ε * ‖T w‖ := by
          field_simp
        rw [heq] at h2
        exact h2
    rcases eq_or_lt_of_le hε with hε0 | hεpos
    · rw [← hε0, zero_mul]
      exact hc0
    · have hTle : ‖T‖ ≤ c / ε := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
        have hb := hbound w
        rw [div_mul_eq_mul_div, le_div_iff₀ hεpos]
        nlinarith [hb]
      have hmulc : ε * (c / ε) = c := by field_simp
      have hfin : ε * ‖T‖ ≤ ε * (c / ε) := mul_le_mul_of_nonneg_left hTle hε
      rwa [hmulc] at hfin

end Linear

/-! ## The cofinal horizon invariant -/

section Horizon

variable {S B I : Type*} [PseudoMetricSpace B] [PseudoMetricSpace I]

/-- **Card `(12)`.**  The cofinal lifting horizon of a family of observer pairs. -/
noncomputable def liftingHorizon {Sn : ℕ → Type*} (p : ∀ n, Sn n → I) (q : ∀ n, Sn n → B) :
    ℝ≥0∞ :=
  ⨅ ε : {ε : ℝ // 0 < ε}, limsup (fun n => liftingModulus (p n) (q n) (ε : ℝ)) atTop

/-- **Card `(15)`.**  If arbitrarily large source separations survive at arbitrarily fine observed
resolution, the horizon is infinite. -/
theorem liftingHorizon_eq_top {Sn : ℕ → Type*} (p : ∀ n, Sn n → I) (q : ∀ n, Sn n → B)
    (h : ∀ ε : ℝ, 0 < ε → ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop, ∃ x y : Sn n,
      dist (q n x) (q n y) ≤ ε ∧ M ≤ dist (p n x) (p n y)) :
    liftingHorizon p q = ⊤ := by
  refine le_antisymm le_top (le_iInf fun ε => ?_)
  refine ge_of_eq (eq_top_of_forall_ofReal_le fun M hM => ?_)
  refine le_limsup_of_frequently_le ((h (ε : ℝ) ε.2 M hM).mono ?_) ?_
  · rintro n ⟨x, y, hq, hp⟩
    exact le_trans (ENNReal.ofReal_le_ofReal hp) (le_liftingModulus _ _ hq)
  · exact ⟨⊤, by simp⟩

end Horizon

/-! ## Recurrence with singular decoding -/

section Counterexample

/-- The exact circle-chord identity. -/
theorem norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hhalf : ((θ : ℂ) * Complex.I) = ((θ / 2 : ℝ) : ℂ) * Complex.I
      + ((θ / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hfac : Complex.exp ((θ : ℂ) * Complex.I) - 1
      = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
          - Complex.exp (-(((θ / 2 : ℝ) : ℂ) * Complex.I))) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add, ← hhalf, add_neg_cancel, Complex.exp_zero]
  have hsin : Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I)
      - Complex.exp (-(((θ / 2 : ℝ) : ℂ) * Complex.I))
      = (2 : ℂ) * (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I]
    rw [Complex.cos_neg, Complex.sin_neg]
    push_cast
    ring
  rw [hfac, hsin, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]

/-- **Card `(13)`.**  The interior observer of the recurrence family. -/
def recurrenceInterior (n : ℕ) (k : Fin (n + 1)) : ℝ := (k : ℕ)

/-- **Card `(13)`.**  The boundary observer of the recurrence family. -/
noncomputable def recurrenceBoundary (n : ℕ) (k : Fin (n + 1)) : ℂ :=
  Complex.exp (((2 * Real.pi * (k : ℕ) / ((n : ℝ) + 1 / n) : ℝ) : ℂ) * Complex.I)

/-- **Card `(14)`.**  The wrap-around chord of the boundary observer, exactly. -/
theorem norm_recurrenceBoundary_sub {n : ℕ} (hn : 0 < n) :
    ‖recurrenceBoundary n (Fin.last n) - recurrenceBoundary n 0‖
      = 2 * |Real.sin (Real.pi * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 + 1))| := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have h0 : recurrenceBoundary n 0 = 1 := by
    simp [recurrenceBoundary]
  have hlast : ((2 * Real.pi * ((Fin.last n : Fin (n+1)) : ℕ) / ((n : ℝ) + 1 / n) : ℝ))
      = 2 * (Real.pi * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 + 1)) := by
    simp only [Fin.val_last]
    field_simp
  rw [h0, recurrenceBoundary, hlast, norm_exp_mul_I_sub_one]
  congr 2
  ring

/-- **Card `(15)`.**  The recurrence family has infinite cofinal lifting horizon: arbitrarily
large interior separation survives at arbitrarily fine boundary resolution. -/
theorem liftingHorizon_recurrence_eq_top :
    liftingHorizon (fun n => recurrenceInterior n) (fun n => recurrenceBoundary n) = ⊤ := by
  refine liftingHorizon_eq_top _ _ fun ε hε M hM => ?_
  refine Filter.Eventually.frequently ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (max (M + 1) (4 * Real.pi / ε))
  filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hnN : N ≤ n := le_trans (le_max_right 1 N) hn
  have hnR : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hnN
  have hMn : M ≤ (n : ℝ) := by
    have := le_trans (le_max_left (M + 1) (4 * Real.pi / ε)) hN.le
    linarith
  have hεn : 4 * Real.pi / ε ≤ (n : ℝ) := by
    have := le_trans (le_max_right (M + 1) (4 * Real.pi / ε)) hN.le
    linarith
  refine ⟨Fin.last n, 0, ?_, ?_⟩
  · rw [dist_eq_norm, norm_recurrenceBoundary_sub hn1]
    have hpos : (0 : ℝ) < (n : ℝ) ^ 2 + 1 := by positivity
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have harg : Real.pi * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 + 1)
        = Real.pi - Real.pi / ((n : ℝ) ^ 2 + 1) := by
      field_simp
      ring
    have hsmall : (0 : ℝ) ≤ Real.pi / ((n : ℝ) ^ 2 + 1) := by positivity
    have hsmall' : Real.pi / ((n : ℝ) ^ 2 + 1) ≤ Real.pi := by
      rw [div_le_iff₀ hpos]
      nlinarith [Real.pi_pos, sq_nonneg ((n : ℝ))]
    rw [harg, Real.sin_pi_sub, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hsmall hsmall')]
    have hbound : Real.sin (Real.pi / ((n : ℝ) ^ 2 + 1)) ≤ Real.pi / ((n : ℝ) ^ 2 + 1) :=
      Real.sin_le hsmall
    have hchain : Real.pi / ((n : ℝ) ^ 2 + 1) ≤ Real.pi / (n : ℝ) := by
      refine div_le_div_of_nonneg_left Real.pi_pos.le hnpos ?_
      nlinarith [hnpos]
    have hfin : 2 * (Real.pi / (n : ℝ)) ≤ ε := by
      rw [div_le_iff₀ hε] at hεn
      rw [mul_div_assoc'] at *
      rw [div_le_iff₀ hnpos]
      nlinarith [Real.pi_pos, hεn]
    linarith
  · rw [Real.dist_eq, recurrenceInterior, recurrenceInterior]
    simp only [Fin.val_last, Fin.val_zero, Nat.cast_zero, sub_zero]
    rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]

/-- The wrap-around chord in the card's reflected form: `2 sin(π/(n²+1))`. -/
theorem norm_recurrenceBoundary_sub' {n : ℕ} (hn : 0 < n) :
    ‖recurrenceBoundary n (Fin.last n) - recurrenceBoundary n 0‖
      = 2 * Real.sin (Real.pi / ((n : ℝ) ^ 2 + 1)) := by
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 + 1 := by positivity
  have harg : Real.pi * (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 + 1)
      = Real.pi - Real.pi / ((n : ℝ) ^ 2 + 1) := by
    field_simp
    ring
  have hsmall : (0 : ℝ) ≤ Real.pi / ((n : ℝ) ^ 2 + 1) := by positivity
  have hsmall' : Real.pi / ((n : ℝ) ^ 2 + 1) ≤ Real.pi := by
    rw [div_le_iff₀ hpos]
    nlinarith [Real.pi_pos, sq_nonneg ((n : ℝ))]
  rw [norm_recurrenceBoundary_sub hn, harg, Real.sin_pi_sub,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hsmall hsmall')]

/-- **Card `(16)`.**  Every exact decoder of the recurrence family is Lipschitz only with a
constant at least `n / (2 sin(π/(n²+1)))`: the source separation is `n` while the observed
separation is the wrap-around chord. -/
theorem lipschitz_decoder_recurrence_ge {n : ℕ} (hn : 0 < n) {K : NNReal} {r : ℂ → ℝ}
    (hr : LipschitzWith K r)
    (hfact : ∀ k : Fin (n + 1), recurrenceInterior n k = r (recurrenceBoundary n k)) :
    (n : ℝ) ≤ (K : ℝ) * (2 * Real.sin (Real.pi / ((n : ℝ) ^ 2 + 1))) := by
  have hmain := dist_le_of_lipschitz_factor hr hfact (Fin.last n) 0
  have hleft : dist (recurrenceInterior n (Fin.last n)) (recurrenceInterior n 0) = (n : ℝ) := by
    rw [Real.dist_eq, recurrenceInterior, recurrenceInterior]
    simp only [Fin.val_last, Fin.val_zero, Nat.cast_zero, sub_zero]
    exact abs_of_nonneg (by positivity)
  have hright : dist (recurrenceBoundary n (Fin.last n)) (recurrenceBoundary n 0)
      = 2 * Real.sin (Real.pi / ((n : ℝ) ^ 2 + 1)) := by
    rw [dist_eq_norm, norm_recurrenceBoundary_sub' hn]
  rwa [hleft, hright] at hmain

/-- **Card `(16)`.**  Consequently the exact-decoder Lipschitz constant of the recurrence family
grows at least like `n³/(2π)`: the horizon is pure loss of uniform conditioning. -/
theorem cube_div_le_lipschitz_decoder_recurrence {n : ℕ} (hn : 0 < n) {K : NNReal} {r : ℂ → ℝ}
    (hr : LipschitzWith K r)
    (hfact : ∀ k : Fin (n + 1), recurrenceInterior n k = r (recurrenceBoundary n k)) :
    (n : ℝ) ^ 3 / (2 * Real.pi) ≤ (K : ℝ) := by
  have hmain := lipschitz_decoder_recurrence_ge hn hr hfact
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 + 1 := by positivity
  have hK : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hsin : Real.sin (Real.pi / ((n : ℝ) ^ 2 + 1)) ≤ Real.pi / ((n : ℝ) ^ 2 + 1) :=
    Real.sin_le (by positivity)
  have hstep : (n : ℝ) ≤ (K : ℝ) * (2 * (Real.pi / ((n : ℝ) ^ 2 + 1))) := by
    refine le_trans hmain ?_
    have := mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) *
      Real.sin (Real.pi / ((n : ℝ) ^ 2 + 1)) ≤ 2 * (Real.pi / ((n : ℝ) ^ 2 + 1))) hK
    exact this
  have hmul : (n : ℝ) * ((n : ℝ) ^ 2 + 1) ≤ (K : ℝ) * (2 * Real.pi) := by
    have h := mul_le_mul_of_nonneg_right hstep hpos.le
    calc (n : ℝ) * ((n : ℝ) ^ 2 + 1)
        ≤ (K : ℝ) * (2 * (Real.pi / ((n : ℝ) ^ 2 + 1))) * ((n : ℝ) ^ 2 + 1) := h
      _ = (K : ℝ) * (2 * Real.pi) := by field_simp
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  nlinarith [hmul, Nat.cast_nonneg (α := ℝ) n]

end Counterexample

end HTGeometry.ConstraintRelativity
