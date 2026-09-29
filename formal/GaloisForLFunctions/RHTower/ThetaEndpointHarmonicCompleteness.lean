import GaloisForLFunctions.RHTower.ThetaEndpointDivisorClassification

/-!
# RH as endpoint harmonic completeness for the literal theta measure

Let `μ = k dx` be the theta measure, `F = XiC = k̂`, and `V` the real span of the jets
`φ_{γ,j}(x) = ∂_t^j cos(tx)|_{t=γ}` over the positive real zeros `γ` of `F` and `j` below their
multiplicity.  Each jet lies in `L^p(μ)` for every finite `p` and has zero `μ`-mean.

**Theorem.**  The following are equivalent:
(i) every zero of `F` is real;
(ii) `span({1} ∪ V)` is dense in `L¹_even(μ)`;
(iii) `span V` is dense in the mean-zero even subspace of `L¹(μ)`.

Proof.  By `L¹–L^∞` duality and Hahn–Banach, density fails exactly when a bounded function
annihilates the span without annihilating the whole target.  After evenization, a bounded even
annihilator `g` gives a real even source `k g`, `|k g| ≤ C k`, whose transform keeps every real zero
of `F` (the jets are the real-zero Taylor coefficients).  Under (i) this is the complete Xi divisor, so
relative-source rigidity makes `g` constant; the mean condition or the mean-zero target finishes.
Conversely a first-quadrant zero `α` gives, by successive complex zero divisions of `k` and a real
part, a nonzero bounded even annihilator with transform `F(z) z² / ((1-z²/α²)(1-z²/ᾱ²))^m`.

The module also provides real defect sources `v_i` with `v̂_i P_L = F z^{2(i+1)}` for any finite set of
first-quadrant zeros, and their linear independence.
-/
open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ## Real defect sources -/

theorem listDivisor_quadrantListOf_ofReal_ne_zero {l : List ℂ}
    (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) (x : ℝ) : listDivisor (quadrantListOf l) x ≠ 0 := by
  obtain ⟨r, hr, hrx⟩ := listDivisor_quadrantListOf_ofReal hl x
  rw [hrx]
  exact_mod_cast hr.ne'

theorem listDivisor_quadrantListOf_ne_zero_of_norm_le_one {l : List ℂ}
    (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    listDivisor (quadrantListOf l) z ≠ 0 := by
  intro h
  obtain ⟨β, hβ, h' | h'⟩ := exists_mem_of_listDivisor_eq_zero h
  · exact XiC_ne_zero_of_norm_le_one hz (h' ▸ XiC_eq_zero_of_mem_quadrantListOf hl hβ)
  · have : XiC z = 0 := by rw [h', XiC_even]; exact XiC_eq_zero_of_mem_quadrantListOf hl hβ
    exact XiC_ne_zero_of_norm_le_one hz this

/-- A transform with `V P_L = F Q` for entire `Q` keeps every real zero of `F`. -/
theorem keepsRealZeros_of_mul_eq {V Q : ℂ → ℂ} (hVd : Differentiable ℂ V)
    (hQd : Differentiable ℂ Q) {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros)
    (h : ∀ z, V z * listDivisor (quadrantListOf l) z = XiC z * Q z) : KeepsRealZeros V := by
  intro γ
  have hP := differentiable_listDivisor (quadrantListOf l)
  have h1 : analyticOrderAt (V * listDivisor (quadrantListOf l)) γ =
      analyticOrderAt (XiC * Q) γ := by
    rw [show V * listDivisor (quadrantListOf l) = XiC * Q from funext h]
  rw [analyticOrderAt_mul (hVd.analyticAt _) (hP.analyticAt _),
    analyticOrderAt_mul (XiC_differentiable.analyticAt _) (hQd.analyticAt _),
    (hP.analyticAt _).analyticOrderAt_eq_zero.2 (listDivisor_quadrantListOf_ofReal_ne_zero hl γ),
    add_zero] at h1
  rw [h1]
  exact le_self_add

/-- **Real defect sources.**  For a duplicate-free list `l` of first-quadrant zeros and
`n ≤ |L|` (`L` the off-line list of `l`), there are real even continuous `k`-dominated sources
`v_i`, `i < n`, with `v̂_i(z) P_L(z) = F(z) z^{2(i+1)}`. -/
theorem exists_defect_sources {l : List ℂ} (hl : ∀ α ∈ l, α ∈ xiQuadrantZeros) (hnd : l.Nodup)
    {n : ℕ} (hn : n ≤ (quadrantListOf l).length) :
    ∃ v : Fin n → ℝ → ℝ, (∀ i, Continuous (v i)) ∧ (∀ i x, v i (-x) = v i x) ∧
      (∃ C, ∀ i x, |v i x| ≤ C * thetaCuspFullSource x) ∧
      ∀ i z, sourceTransform (fun x => (v i x : ℂ)) z * listDivisor (quadrantListOf l) z =
        XiC z * z ^ (2 * ((i : ℕ) + 1)) := by
  have hL := thetaDivisionList_quadrantListOf hl hnd
  have h : ∀ i : Fin n, ∃ u : ℝ → ℂ, ExpMomentSource u ∧ (∀ x, u (-x) = u x) ∧
      (∃ C, ∀ x, ‖u x‖ ≤ C * thetaCuspFullSource x) ∧
      ∀ z, sourceTransform u z * listDivisor (quadrantListOf l) z =
        XiC z * (Polynomial.X ^ ((i : ℕ) + 1) : Polynomial ℂ).eval (z ^ 2) := fun i => by
    obtain ⟨u, hu1, hu2, hu3, hu4, -⟩ := exists_source_mul_listDivisor hL
      (Polynomial.X ^ ((i : ℕ) + 1)) (by rw [Polynomial.natDegree_X_pow]; omega)
    exact ⟨u, hu1, hu2, hu3, hu4⟩
  choose u hum hue huC huT using h
  choose Cu hCu using huC
  refine ⟨fun i x => (u i x).re, fun i => Complex.continuous_re.comp (hum i).continuous,
    fun i x => by simp only [hue], ⟨∑ i, max (Cu i) 0, fun i x => ?_⟩, fun i z => ?_⟩
  · calc |(u i x).re| ≤ ‖u i x‖ := Complex.abs_re_le_norm _
      _ ≤ Cu i * thetaCuspFullSource x := hCu i x
      _ ≤ max (Cu i) 0 * thetaCuspFullSource x :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (thetaCuspFullSource_pos x).le
      _ ≤ (∑ j, max (Cu j) 0) * thetaCuspFullSource x :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => le_max_right (Cu j) 0)
            (Finset.mem_univ i)) (thetaCuspFullSource_pos x).le
  · rw [sourceTransform_ofReal_re (hum i) (hue i)]
    have h1 := huT i z
    have h2 := congrArg (starRingEnd ℂ) (huT i ((starRingEnd ℂ) z))
    simp only [Polynomial.eval_pow, Polynomial.eval_X, map_mul, map_pow, XiC_conj,
      Complex.conj_conj, listDivisor_quadrantListOf_conj] at h1 h2
    rw [div_mul_eq_mul_div, add_mul, h1, h2, ← pow_mul, mul_comm 2]
    ring

/-- The mean of a source is its transform at `0`. -/
theorem sourceTransform_zero_ofReal (v : ℝ → ℝ) :
    sourceTransform (fun x => (v x : ℂ)) 0 = ((∫ x, v x : ℝ) : ℂ) := by
  unfold sourceTransform
  simp only [mul_zero, zero_mul, Complex.exp_zero, one_mul]
  exact integral_ofReal

theorem integral_eq_zero_of_mul_eq {v : ℝ → ℝ} {l : List ℂ} {k : ℕ} (hk : 0 < k)
    (h : ∀ z, sourceTransform (fun x => (v x : ℂ)) z * listDivisor (quadrantListOf l) z =
      XiC z * z ^ k) : ∫ x, v x = 0 := by
  have h0 := h 0
  rw [listDivisor_zero, mul_one, zero_pow hk.ne', mul_zero, sourceTransform_zero_ofReal] at h0
  exact_mod_cast h0

theorem sourceTransform_finset_sum_ofReal {ι : Type*} (s : Finset ι) {v : ι → ℝ → ℝ}
    (hv : ∀ i ∈ s, AEStronglyMeasurable (v i)) {C : ι → ℝ}
    (hC : ∀ i ∈ s, ∀ x, |v i x| ≤ C i * thetaCuspFullSource x) (c : ι → ℝ) (z : ℂ) :
    sourceTransform (fun x => ((∑ i ∈ s, c i * v i x : ℝ) : ℂ)) z =
      ∑ i ∈ s, (c i : ℂ) * sourceTransform (fun x => (v i x : ℂ)) z := by
  have hint : ∀ i ∈ s, Integrable fun x : ℝ => Complex.exp (-I * z * x) * ((c i : ℂ) * (v i x : ℂ)) :=
    fun i hi => by
      have hms := measurableMomentSource_of_le
        (Complex.continuous_ofReal.comp_aestronglyMeasurable (hv i hi)) fun x => by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact hC i hi x
      exact ((hms.integrable_cexp z).const_mul (c i : ℂ)).congr
        (Eventually.of_forall fun x => by simp only; ring)
  unfold sourceTransform
  simp only
  have hsum : ∑ i ∈ s, (c i : ℂ) * ∫ x : ℝ, Complex.exp (-I * z * x) * (v i x : ℂ) =
      ∑ i ∈ s, ∫ x : ℝ, Complex.exp (-I * z * x) * ((c i : ℂ) * (v i x : ℂ)) :=
    Finset.sum_congr rfl fun i _ => by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [hsum, ← integral_finsetSum s hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  push_cast
  rw [Finset.mul_sum]

/-- **Independence of the defect sources.** -/
theorem defect_sources_independent {l : List ℂ} {n : ℕ}
    {v : Fin n → ℝ → ℝ} (hvc : ∀ i, Continuous (v i)) {C : ℝ}
    (hvC : ∀ i x, |v i x| ≤ C * thetaCuspFullSource x)
    (hvT : ∀ i z, sourceTransform (fun x => (v i x : ℂ)) z * listDivisor (quadrantListOf l) z =
      XiC z * z ^ (2 * ((i : ℕ) + 1)))
    (c : Fin n → ℝ) (h : ∀ x, ∑ i, c i * v i x = 0) : c = 0 := by
  have hT : ∀ z, ∑ i, (c i : ℂ) * sourceTransform (fun x => (v i x : ℂ)) z = 0 := by
    intro z
    rw [← sourceTransform_finset_sum_ofReal Finset.univ (fun i _ => (hvc i).aestronglyMeasurable)
      (fun i _ => hvC i) c z]
    simp only [h, Complex.ofReal_zero]
    unfold sourceTransform
    simp
  set q : Polynomial ℂ := ∑ i : Fin n, Polynomial.C (c i : ℂ) * Polynomial.X ^ (2 * ((i : ℕ) + 1))
  have hq : q = 0 := by
    refine Polynomial.eq_of_infinite_eval_eq q 0 ?_
    refine ((Set.Icc_infinite (zero_lt_one' ℝ)).image Complex.ofReal_injective.injOn).mono ?_
    rintro _ ⟨t, ht, rfl⟩
    have hz : ‖(t : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg ht.1]; exact ht.2
    simp only [mem_setOf_eq, Polynomial.eval_zero, q, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have h1 := hT t
    have h2 : (∑ i, (c i : ℂ) * sourceTransform (fun x => (v i x : ℂ)) t) *
        listDivisor (quadrantListOf l) t = XiC t * ∑ i, (c i : ℂ) * (t : ℂ) ^ (2 * ((i : ℕ) + 1)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, hvT i t]; ring
    rw [h1, zero_mul] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (XiC_ne_zero_of_norm_le_one hz)
  funext i
  have := congrArg (fun p : Polynomial ℂ => p.coeff (2 * ((i : ℕ) + 1))) hq
  simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i (fun b _ hb => if_neg (by
    intro h'; exact hb (Fin.ext (by omega)))) (fun h' => absurd (Finset.mem_univ i) h'),
    if_pos rfl] at this
  exact_mod_cast this

/-! ## The even `L¹` space of the theta measure -/

/-- `L¹(μ)` for the theta measure. -/
abbrev ThetaL1 := Lp ℝ 1 thetaSourceMeasure

/-- The reflection `f ↦ f(-·)` on `L¹(μ)`. -/
def thetaReflectL1 : ThetaL1 →L[ℝ] ThetaL1 :=
  (Lp.compMeasurePreservingₗᵢ ℝ Neg.neg
    (Measure.measurePreserving_neg thetaSourceMeasure)).toContinuousLinearMap

/-- The even subspace `L¹_even(μ)`. -/
def thetaEvenL1 : Submodule ℝ ThetaL1 :=
  LinearMap.ker ((thetaReflectL1 - ContinuousLinearMap.id ℝ ThetaL1 : ThetaL1 →L[ℝ] ThetaL1) :
    ThetaL1 →ₗ[ℝ] ThetaL1)

theorem isClosed_thetaEvenL1 : IsClosed (thetaEvenL1 : Set ThetaL1) :=
  (thetaReflectL1 - ContinuousLinearMap.id ℝ ThetaL1).isClosed_ker

theorem coeFn_thetaReflectL1 (f : ThetaL1) :
    (thetaReflectL1 f : ℝ → ℝ) =ᵐ[thetaSourceMeasure] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f _

theorem mem_thetaEvenL1_iff {f : ThetaL1} :
    f ∈ thetaEvenL1 ↔ (fun x => f (-x)) =ᵐ[thetaSourceMeasure] f := by
  simp only [thetaEvenL1, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply,
    ContinuousLinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h
    filter_upwards [coeFn_thetaReflectL1 f, show (thetaReflectL1 f : ℝ → ℝ) =ᵐ[_] f from by
      rw [h]] with x h1 h2
    rw [← h1, h2]
  · intro h
    refine Lp.ext ?_
    filter_upwards [coeFn_thetaReflectL1 f, h] with x h1 h2
    rw [h1, h2]

theorem toLp_mem_thetaEvenL1 {g : ℝ → ℝ} (hg : MemLp g 1 thetaSourceMeasure)
    (heven : ∀ x, g (-x) = g x) : hg.toLp g ∈ thetaEvenL1 := by
  rw [mem_thetaEvenL1_iff]
  have h1 := MemLp.coeFn_toLp hg
  have h2 : (fun x => (hg.toLp g : ℝ → ℝ) (-x)) =ᵐ[thetaSourceMeasure] fun x => g (-x) :=
    (Measure.measurePreserving_neg thetaSourceMeasure).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx2, heven, hx1]

/-! ## Jets and constants in `L¹(μ)` -/

theorem integrable_exp_mul_abs_thetaSourceMeasure (r : ℝ) :
    Integrable (fun x => Real.exp (r * |x|)) thetaSourceMeasure := by
  rw [integrable_thetaSourceMeasure_iff]
  refine (expMomentSource_thetaSourceC.moment r).congr (Eventually.of_forall fun x => ?_)
  simp only [thetaSourceC, Complex.norm_real, Real.norm_of_nonneg (thetaCuspFullSource_pos x).le]
  ring

theorem abs_pow_le_factorial_mul_exp (x : ℝ) (j : ℕ) :
    |x| ^ j ≤ j.factorial * Real.exp |x| := by
  have h := Real.pow_div_factorial_le_exp (|x|) (abs_nonneg x) j
  rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos j)] at h
  linarith

/-- Every real-zero jet belongs to `L^p(μ)` for every finite `p`. -/
theorem memLp_thetaCosJet (γ : ℝ) (j : ℕ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (thetaCosJet γ j) p thetaSourceMeasure := by
  have hm : AEStronglyMeasurable (thetaCosJet γ j) thetaSourceMeasure :=
    (continuous_thetaCosJet γ j).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLp_zero_iff_aestronglyMeasurable.2 hm
  rw [← integrable_norm_rpow_iff hm hp0 hp]
  set r := p.toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  refine ((integrable_exp_mul_abs_thetaSourceMeasure r).const_mul ((j.factorial : ℝ) ^ r)).mono'
    ((continuous_thetaCosJet γ j).norm.rpow_const fun _ => Or.inr hr).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  calc |thetaCosJet γ j x| ^ r ≤ (j.factorial * Real.exp |x|) ^ r :=
        Real.rpow_le_rpow (abs_nonneg _) ((abs_thetaCosJet_le γ j x).trans
          (abs_pow_le_factorial_mul_exp x j)) hr
    _ = (j.factorial : ℝ) ^ r * Real.exp (r * |x|) := by
        rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul, mul_comm |x|]

/-- The jets at a zero have vanishing `μ`-mean: `∫ φ_{γ,j} dμ = F^{(j)}(γ) = 0` for `j` below the
multiplicity. -/
theorem integral_thetaCosJet_thetaSourceMeasure {γ : ℝ} {j : ℕ}
    (hj : (j : ℕ∞) < analyticOrderAt XiC γ) : ∫ x, thetaCosJet γ j x ∂thetaSourceMeasure = 0 := by
  have h := iteratedDeriv_sourceTransform_ofReal (v := thetaCuspFullSource)
    contDiff_thetaCuspFullSource.continuous.aestronglyMeasurable (C := 1)
    (fun x => by rw [abs_of_pos (thetaCuspFullSource_pos x), one_mul]) thetaCuspFullSource_neg γ j
  have hk : (sourceTransform fun x => (thetaCuspFullSource x : ℂ)) = XiC :=
    funext sourceTransform_thetaSourceC
  rw [hk] at h
  have h0 : iteratedDeriv j XiC γ = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (XiC_differentiable.analyticAt _)).1
      (by exact_mod_cast Order.add_one_le_of_lt hj) j (by omega)
  rw [h0] at h
  rw [integral_thetaSourceMeasure]
  have : ∫ x, thetaCosJet γ j x * thetaCuspFullSource x = 0 := by exact_mod_cast h.symm
  rw [← this]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

/-- The jet `φ_{γ,j}` as an element of `L¹(μ)`. -/
def thetaJetL1 (γ : ℝ) (j : ℕ) : ThetaL1 := (memLp_thetaCosJet γ j ENNReal.one_ne_top).toLp _

/-- The constant `1` in `L¹(μ)`. -/
def thetaOneL1 : ThetaL1 := (memLp_const (1 : ℝ)).toLp fun _ => (1 : ℝ)

/-- The real-zero jets `φ_{γ,j}`, `γ > 0` a zero of `F`, `j` below its multiplicity. -/
def thetaJetSet : Set ThetaL1 :=
  {f | ∃ γ : ℝ, 0 < γ ∧ XiC γ = 0 ∧ ∃ j : ℕ, (j : ℕ∞) < analyticOrderAt XiC γ ∧ f = thetaJetL1 γ j}

/-- `span V`. -/
def thetaJetSpan : Submodule ℝ ThetaL1 := Submodule.span ℝ thetaJetSet

/-- `span({1} ∪ V)`. -/
def thetaJetOneSpan : Submodule ℝ ThetaL1 := Submodule.span ℝ (insert thetaOneL1 thetaJetSet)

/-- The mean `f ↦ ∫ f dμ` on `L¹(μ)`. -/
def thetaMeanL1 : ThetaL1 →L[ℝ] ℝ := L1.integralCLM

theorem thetaMeanL1_apply (f : ThetaL1) : thetaMeanL1 f = ∫ x, f x ∂thetaSourceMeasure := by
  rw [← L1.integral_eq_integral, L1.integral_eq]
  rfl

/-- The mean-zero even subspace `{h ∈ L¹_even(μ) : ∫ h dμ = 0}`. -/
def thetaEvenMeanZeroL1 : Submodule ℝ ThetaL1 :=
  thetaEvenL1 ⊓ LinearMap.ker (thetaMeanL1 : ThetaL1 →ₗ[ℝ] ℝ)

theorem isClosed_thetaEvenMeanZeroL1 : IsClosed (thetaEvenMeanZeroL1 : Set ThetaL1) :=
  isClosed_thetaEvenL1.inter thetaMeanL1.isClosed_ker

theorem thetaJetL1_mem_thetaEvenL1 (γ : ℝ) (j : ℕ) : thetaJetL1 γ j ∈ thetaEvenL1 :=
  toLp_mem_thetaEvenL1 _ (thetaCosJet_neg γ j)

theorem thetaOneL1_mem_thetaEvenL1 : thetaOneL1 ∈ thetaEvenL1 :=
  toLp_mem_thetaEvenL1 _ fun _ => rfl

theorem thetaJetSet_subset_thetaEvenMeanZeroL1 :
    thetaJetSet ⊆ (thetaEvenMeanZeroL1 : Set ThetaL1) := by
  rintro f ⟨γ, -, -, j, hj, rfl⟩
  refine ⟨thetaJetL1_mem_thetaEvenL1 γ j, ?_⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, thetaMeanL1_apply]
  unfold thetaJetL1
  rw [integral_congr_ae (MemLp.coeFn_toLp _)]
  exact integral_thetaCosJet_thetaSourceMeasure hj

theorem thetaJetOneSpan_le_thetaEvenL1 : thetaJetOneSpan ≤ thetaEvenL1 := by
  refine Submodule.span_le.2 ?_
  rintro f (rfl | hf)
  · exact thetaOneL1_mem_thetaEvenL1
  · exact (thetaJetSet_subset_thetaEvenMeanZeroL1 hf).1

theorem thetaJetSpan_le_thetaEvenMeanZeroL1 : thetaJetSpan ≤ thetaEvenMeanZeroL1 :=
  Submodule.span_le.2 thetaJetSet_subset_thetaEvenMeanZeroL1

/-! ## Bounded annihilators as divisor-keeping sources -/

theorem integral_mul_toLp (g : ℝ → ℝ) {f : ℝ → ℝ} (hf : MemLp f 1 thetaSourceMeasure) :
    ∫ x, g x * (hf.toLp f) x ∂thetaSourceMeasure = ∫ x, g x * f x ∂thetaSourceMeasure :=
  integral_congr_ae ((MemLp.coeFn_toLp hf).mono fun x hx => by simp only [hx])

theorem integrable_bounded_mul_thetaL1 {h : ℝ → ℝ} (hm : Measurable h) {C : ℝ} (hb : ∀ x, |h x| ≤ C)
    (f : ThetaL1) : Integrable (fun x => h x * f x) thetaSourceMeasure :=
  (L1.integrable_coeFn f).bdd_mul hm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

/-- **Evenization.**  On even functions a bounded annihilator is represented by an everywhere
bounded even measurable function. -/
theorem exists_even_representative {g : ℝ → ℝ} (hgm : StronglyMeasurable g) {C : ℝ}
    (hgC : ∀ᵐ x ∂thetaSourceMeasure, |g x| ≤ C) :
    ∃ g' : ℝ → ℝ, Measurable g' ∧ (∀ x, g' (-x) = g' x) ∧ (∀ x, |g' x| ≤ max C 0) ∧
      ∀ f ∈ thetaEvenL1, ∫ x, g x * f x ∂thetaSourceMeasure =
        ∫ x, g' x * f x ∂thetaSourceMeasure := by
  set T : ℝ → ℝ := fun x => if |g x| ≤ C then g x else 0 with hTdef
  have hTm : Measurable T := Measurable.ite
    (measurableSet_le hgm.measurable.abs measurable_const) hgm.measurable measurable_const
  have hTb : ∀ x, |T x| ≤ max C 0 := fun x => by
    simp only [T]
    split_ifs with h
    · exact h.trans (le_max_left _ _)
    · simp
  have hTg : ∀ᵐ x ∂thetaSourceMeasure, g x = T x := hgC.mono fun x hx => by simp only [T, if_pos hx]
  refine ⟨fun x => (T x + T (-x)) / 2, (hTm.add (hTm.comp measurable_neg)).div_const 2,
    fun x => by simp only [neg_neg]; ring, fun x => ?_, fun f hf => ?_⟩
  · rw [abs_div, abs_two, div_le_iff₀ two_pos]
    calc |T x + T (-x)| ≤ |T x| + |T (-x)| := abs_add_le _ _
      _ ≤ max C 0 + max C 0 := add_le_add (hTb x) (hTb (-x))
      _ = max C 0 * 2 := by ring
  · have hfe := mem_thetaEvenL1_iff.1 hf
    have hint1 := integrable_bounded_mul_thetaL1 hTm hTb f
    have hint2 : Integrable (fun x => T (-x) * f x) thetaSourceMeasure :=
      integrable_bounded_mul_thetaL1 (hTm.comp measurable_neg) (fun x => hTb (-x)) f
    have h1 : ∫ x, g x * f x ∂thetaSourceMeasure = ∫ x, T x * f x ∂thetaSourceMeasure :=
      integral_congr_ae (hTg.mono fun x hx => by simp only [hx])
    have h2 : ∫ x, T (-x) * f x ∂thetaSourceMeasure = ∫ x, T x * f x ∂thetaSourceMeasure := by
      have h := integral_neg_eq_self (fun x => T x * f (-x)) thetaSourceMeasure
      simp only [neg_neg] at h
      rw [h]
      exact integral_congr_ae (hfe.mono fun x hx => by simp only at hx ⊢; rw [hx])
    rw [h1]
    have h3 : ∫ x, (T x + T (-x)) / 2 * f x ∂thetaSourceMeasure =
        (∫ x, T x * f x ∂thetaSourceMeasure + ∫ x, T (-x) * f x ∂thetaSourceMeasure) / 2 := by
      rw [← integral_add hint1 hint2, ← integral_div]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    rw [h3, h2]
    ring

theorem annihilates_span_iff {T : Set ThetaL1} {g : ℝ → ℝ} (hgm : Measurable g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) :
    (∀ s ∈ Submodule.span ℝ T, ∫ x, g x * s x ∂thetaSourceMeasure = 0) ↔
      ∀ s ∈ T, ∫ x, g x * s x ∂thetaSourceMeasure = 0 := by
  set ℓ := GaloisForLFunctions.HTGeometry.linftyPairing g hgm.stronglyMeasurable C
    (ae_of_all _ hgC)
  have hℓ : ∀ s, ℓ s = ∫ x, g x * s x ∂thetaSourceMeasure :=
    GaloisForLFunctions.HTGeometry.linftyPairing_apply g _ C _
  constructor
  · exact fun h s hs => h s (Submodule.subset_span hs)
  · intro h s hs
    have hle : Submodule.span ℝ T ≤ LinearMap.ker (ℓ : ThetaL1 →ₗ[ℝ] ℝ) :=
      Submodule.span_le.2 fun t ht => by
        simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hℓ]
        exact h t ht
    have := hle hs
    simpa [hℓ] using this

theorem integral_mul_thetaOneL1 (g : ℝ → ℝ) :
    ∫ x, g x * thetaOneL1 x ∂thetaSourceMeasure = ∫ x, thetaCuspFullSource x * g x := by
  rw [thetaOneL1, integral_mul_toLp, integral_thetaSourceMeasure]
  simp

theorem integral_mul_thetaJetL1 (g : ℝ → ℝ) (γ : ℝ) (j : ℕ) :
    ∫ x, g x * thetaJetL1 γ j x ∂thetaSourceMeasure =
      ∫ x, thetaCosJet γ j x * (thetaCuspFullSource x * g x) := by
  rw [thetaJetL1, integral_mul_toLp, integral_thetaSourceMeasure]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

theorem source_of_bounded {g : ℝ → ℝ} {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    ∀ x, |thetaCuspFullSource x * g x| ≤ C * thetaCuspFullSource x := fun x => by
  rw [abs_mul, abs_of_pos (thetaCuspFullSource_pos x), mul_comm]
  exact mul_le_mul_of_nonneg_right (hgC x) (thetaCuspFullSource_pos x).le

/-- **Annihilators of the jets** are the bounded even `g` for which `k g` keeps the real zeros. -/
theorem annihilates_thetaJetSpan_iff {g : ℝ → ℝ} (hgm : Measurable g)
    (heven : ∀ x, g (-x) = g x) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    (∀ s ∈ thetaJetSpan, ∫ x, g x * s x ∂thetaSourceMeasure = 0) ↔
      KeepsRealZeros (sourceTransform fun x => ((thetaCuspFullSource x * g x : ℝ) : ℂ)) := by
  rw [thetaJetSpan, annihilates_span_iff hgm hgC,
    keepsRealZeros_iff_jets (v := fun x => thetaCuspFullSource x * g x)
      ((contDiff_thetaCuspFullSource.continuous.measurable.mul hgm).aestronglyMeasurable)
      (source_of_bounded hgC)
      (fun x => by simp only [thetaCuspFullSource_neg, heven])]
  constructor
  · intro h γ hγ hz j hj
    rw [← integral_mul_thetaJetL1]
    exact h _ ⟨γ, hγ, hz, j, hj, rfl⟩
  · rintro h _ ⟨γ, hγ, hz, j, hj, rfl⟩
    rw [integral_mul_thetaJetL1]
    exact h γ hγ hz j hj

/-- **Annihilators of `{1} ∪ V`** additionally have zero `μ`-mean. -/
theorem annihilates_thetaJetOneSpan_iff {g : ℝ → ℝ} (hgm : Measurable g)
    (heven : ∀ x, g (-x) = g x) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    (∀ s ∈ thetaJetOneSpan, ∫ x, g x * s x ∂thetaSourceMeasure = 0) ↔
      ∫ x, thetaCuspFullSource x * g x = 0 ∧
        KeepsRealZeros (sourceTransform fun x => ((thetaCuspFullSource x * g x : ℝ) : ℂ)) := by
  rw [← annihilates_thetaJetSpan_iff hgm heven hgC, thetaJetOneSpan, thetaJetSpan,
    annihilates_span_iff hgm hgC, annihilates_span_iff hgm hgC]
  simp only [Set.mem_insert_iff, forall_eq_or_imp, integral_mul_thetaOneL1]

/-! ## The endpoint equivalence -/

/-- Under RH, a bounded even `g` whose source `k g` keeps the real zeros is `μ`-a.e. constant. -/
theorem ae_eq_const_of_keepsRealZeros (hRH : ∀ z, XiC z = 0 → z.im = 0) {g : ℝ → ℝ}
    (hgm : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C)
    (hkeep : KeepsRealZeros (sourceTransform fun x => ((thetaCuspFullSource x * g x : ℝ) : ℂ))) :
    ∃ c : ℝ, ∀ᵐ x ∂thetaSourceMeasure, g x = c := by
  have hdiv : ∀ z, analyticOrderAt XiC z ≤
      analyticOrderAt (sourceTransform fun x => ((thetaCuspFullSource x * g x : ℝ) : ℂ)) z := by
    intro z
    by_cases hz : XiC z = 0
    · have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hRH z hz]
      rw [hzr]
      exact hkeep z.re
    · rw [(XiC_differentiable.analyticAt z).analyticOrderAt_eq_zero.2 hz]
      exact zero_le
  obtain ⟨c, hc⟩ := relativeSource_rigidity_real (v := fun x => thetaCuspFullSource x * g x)
    ((contDiff_thetaCuspFullSource.continuous.measurable.mul hgm).aestronglyMeasurable)
    (source_of_bounded hgC) hdiv
  refine ⟨c, ae_thetaSourceMeasure_iff.2 (hc.mono fun x hx => ?_)⟩
  have hk := thetaCuspFullSource_pos x
  simp only at hx
  rw [mul_comm c] at hx
  exact mul_left_cancel₀ hk.ne' hx

theorem one_le_xiZeroMult {α : ℂ} (hα : XiC α = 0) : 1 ≤ xiZeroMult α := by
  have h : (1 : ℕ∞) ≤ analyticOrderAt XiC α := by
    rw [Order.one_le_iff_ne_zero, Ne, (XiC_differentiable.analyticAt α).analyticOrderAt_eq_zero]
    simpa using hα
  rw [← xiZeroMult_eq] at h
  exact_mod_cast h

/-- **The off-line annihilator.**  A first-quadrant zero `α` yields a continuous even bounded `g`,
not `μ`-a.e. zero, annihilating `1` and every real-zero jet: `k g` has transform
`F(z) z² / ((1 - z²/α²)(1 - z²/ᾱ²))^m`. -/
theorem exists_offLine_annihilator {α : ℂ} (hα : α ∈ xiQuadrantZeros) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, g (-x) = g x) ∧ (∃ C, ∀ x, |g x| ≤ C) ∧
      (∀ s ∈ thetaJetOneSpan, ∫ x, g x * s x ∂thetaSourceMeasure = 0) ∧
      0 < ∫ x, g x * g x ∂thetaSourceMeasure := by
  have hl : ∀ a ∈ [α], a ∈ xiQuadrantZeros := fun a ha => by
    rw [List.mem_singleton] at ha; rw [ha]; exact hα
  have hlen : 1 ≤ (quadrantListOf [α]).length := by
    rw [length_quadrantListOf]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have := one_le_xiZeroMult hα.2.2
    omega
  obtain ⟨v, hvc, hve, ⟨C, hvC⟩, hvT⟩ := exists_defect_sources hl (List.nodup_singleton α) hlen
  set w := v 0
  set g : ℝ → ℝ := fun x => w x / thetaCuspFullSource x
  have hk := fun x => thetaCuspFullSource_pos x
  have hkg : ∀ x, thetaCuspFullSource x * g x = w x := fun x => by
    simp only [g]; rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ (hk x).ne'
  have hgc : Continuous g :=
    (hvc 0).div contDiff_thetaCuspFullSource.continuous fun x => (hk x).ne'
  have hgb : ∀ x, |g x| ≤ C := fun x => by
    simp only [g, abs_div, abs_of_pos (hk x)]
    rw [div_le_iff₀ (hk x)]; exact hvC 0 x
  have hge : ∀ x, g (-x) = g x := fun x => by
    simp only [g]; rw [show w (-x) = w x from hve 0 x, thetaCuspFullSource_neg]
  have hwT := hvT 0
  simp only [Fin.val_zero, zero_add, mul_one] at hwT
  have hVfun : (sourceTransform fun x => ((thetaCuspFullSource x * g x : ℝ) : ℂ)) =
      sourceTransform fun x => (w x : ℂ) := by simp only [hkg]
  have hwm : AEStronglyMeasurable w := (hvc 0).aestronglyMeasurable
  have hwms := measurableMomentSource_of_le (Complex.continuous_ofReal.comp_aestronglyMeasurable hwm)
    fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hvC 0 x
  refine ⟨g, hgc, hge, ⟨C, hgb⟩, (annihilates_thetaJetOneSpan_iff hgc.measurable hge hgb).2
    ⟨?_, ?_⟩, ?_⟩
  · simp only [hkg]
    exact integral_eq_zero_of_mul_eq (by norm_num) hwT
  · rw [hVfun]
    exact keepsRealZeros_of_mul_eq hwms.differentiable_sourceTransform
      (by fun_prop : Differentiable ℂ fun z : ℂ => z ^ 2) hl hwT
  · have hne : ∃ x, g x ≠ 0 := by
      by_contra hall
      push Not at hall
      have hw0 : ∀ x, w x = 0 := fun x => by rw [← hkg, hall x, mul_zero]
      have h := hwT (1 / 2)
      have hzero : sourceTransform (fun x => (w x : ℂ)) (1 / 2) = 0 := by
        unfold sourceTransform; simp [hw0]
      rw [hzero, zero_mul] at h
      have hX := XiC_ne_zero_of_norm_le_one (z := 1 / 2) (by norm_num)
      have : XiC (1 / 2) * (1 / 2 : ℂ) ^ 2 ≠ 0 := mul_ne_zero hX (by norm_num)
      exact this h.symm
    obtain ⟨x₀, hx₀⟩ := hne
    rw [integral_thetaSourceMeasure]
    have hnn : 0 ≤ fun x => thetaCuspFullSource x * (g x * g x) := fun x =>
      mul_nonneg (hk x).le (mul_self_nonneg _)
    have hkc := contDiff_thetaCuspFullSource.continuous
    have hint : Integrable fun x => thetaCuspFullSource x * (g x * g x) := by
      refine ((HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource 0).const_mul
        (C * C)).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hk x), abs_mul]
      have h1 := hgb x
      have h2 : |g x| * |g x| ≤ C * C := mul_le_mul h1 h1 (abs_nonneg _) ((abs_nonneg _).trans h1)
      simp only [zero_mul, Real.exp_zero, one_mul]
      nlinarith [hk x]
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hopen : IsOpen (Function.support fun x => thetaCuspFullSource x * (g x * g x)) :=
      isOpen_ne_fun (by fun_prop) continuous_const
    refine hopen.measure_pos volume ⟨x₀, ?_⟩
    simp only [Function.mem_support]
    exact mul_ne_zero (hk x₀).ne' (mul_ne_zero hx₀ hx₀)

theorem toLp_of_bounded {g : ℝ → ℝ} (hgc : Continuous g) {C : ℝ} (hgb : ∀ x, |g x| ≤ C) :
    MemLp g 1 thetaSourceMeasure :=
  memLp_one_iff_integrable.2 ((integrable_const C).mono' hgc.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgb x))

/-- **RH is endpoint harmonic completeness, (i) ⇔ (ii).**  All zeros of `F` are real iff
`span({1} ∪ V)` is dense in `L¹_even(μ)`. -/
theorem xiReal_iff_closure_thetaJetOneSpan :
    (∀ z, XiC z = 0 → z.im = 0) ↔ thetaJetOneSpan.topologicalClosure = thetaEvenL1 := by
  constructor
  · intro hRH
    refine le_antisymm (Submodule.topologicalClosure_minimal _ thetaJetOneSpan_le_thetaEvenL1
      isClosed_thetaEvenL1) fun w hw => ?_
    rw [GaloisForLFunctions.HTGeometry.mem_topologicalClosure_iff_linfty]
    intro g hgm ⟨C, hgC⟩ hS
    obtain ⟨g', hg'm, hg'e, hg'b, hrep⟩ := exists_even_representative hgm hgC
    have hS' : ∀ s ∈ thetaJetOneSpan, ∫ x, g' x * s x ∂thetaSourceMeasure = 0 := fun s hs => by
      rw [← hrep s (thetaJetOneSpan_le_thetaEvenL1 hs)]; exact hS s hs
    obtain ⟨hmean, hkeep⟩ := (annihilates_thetaJetOneSpan_iff hg'm hg'e hg'b).1 hS'
    obtain ⟨c, hc⟩ := ae_eq_const_of_keepsRealZeros hRH hg'm hg'b hkeep
    have hc0 : c = 0 := by
      have h1 := hS' thetaOneL1 (Submodule.subset_span (Set.mem_insert _ _))
      rw [integral_mul_thetaOneL1, ← integral_thetaSourceMeasure] at h1
      rw [integral_congr_ae hc, integral_const, smul_eq_mul] at h1
      have hμ : 0 < (thetaSourceMeasure univ).toReal := by
        rw [ENNReal.toReal_pos_iff]
        refine ⟨?_, measure_lt_top _ _⟩
        rw [thetaSourceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        refine lt_of_lt_of_le ?_ (lintegral_mono fun x => le_refl _)
        rw [lintegral_pos_iff_support (measurable_thetaSourceDensity.coe_nnreal_ennreal)]
        have : Function.support (fun x => (thetaSourceDensity x : ℝ≥0∞)) = univ :=
          Set.eq_univ_of_forall fun x => by
            simp [thetaSourceDensity, thetaCuspFullSource_pos x]
        rw [this]; simp
      simp only [Measure.real] at h1
      exact (mul_eq_zero.1 h1).resolve_left hμ.ne'
    have hcw : ∫ x, g' x * w x ∂thetaSourceMeasure = ∫ x, c * w x ∂thetaSourceMeasure :=
      integral_congr_ae (hc.mono fun x hx => by simp only [hx])
    rw [hrep w hw, hcw, hc0]
    simp
  · intro hcl
    by_contra hRH
    push Not at hRH
    obtain ⟨z, hz, him⟩ := hRH
    obtain ⟨α, hα, -⟩ := exists_mem_xiQuadrantZeros hz him
    obtain ⟨g, hgc, hge, ⟨C, hgb⟩, hann, hpos⟩ := exists_offLine_annihilator hα
    have hgL := toLp_of_bounded hgc hgb
    have hmem : hgL.toLp g ∈ thetaJetOneSpan.topologicalClosure := by
      rw [hcl]; exact toLp_mem_thetaEvenL1 hgL hge
    have h := (GaloisForLFunctions.HTGeometry.mem_topologicalClosure_iff_linfty.1 hmem) g
      hgc.stronglyMeasurable ⟨C, ae_of_all _ hgb⟩ hann
    rw [integral_mul_toLp] at h
    linarith

/-- **(i) ⇔ (iii).**  All zeros of `F` are real iff `span V` is dense in the mean-zero even
subspace of `L¹(μ)`. -/
theorem xiReal_iff_closure_thetaJetSpan :
    (∀ z, XiC z = 0 → z.im = 0) ↔ thetaJetSpan.topologicalClosure = thetaEvenMeanZeroL1 := by
  constructor
  · intro hRH
    refine le_antisymm (Submodule.topologicalClosure_minimal _ thetaJetSpan_le_thetaEvenMeanZeroL1
      isClosed_thetaEvenMeanZeroL1) fun w hw => ?_
    rw [GaloisForLFunctions.HTGeometry.mem_topologicalClosure_iff_linfty]
    intro g hgm ⟨C, hgC⟩ hS
    obtain ⟨g', hg'm, hg'e, hg'b, hrep⟩ := exists_even_representative hgm hgC
    have hS' : ∀ s ∈ thetaJetSpan, ∫ x, g' x * s x ∂thetaSourceMeasure = 0 := fun s hs => by
      rw [← hrep s (thetaJetSpan_le_thetaEvenMeanZeroL1 hs).1]; exact hS s hs
    have hkeep := (annihilates_thetaJetSpan_iff hg'm hg'e hg'b).1 hS'
    obtain ⟨c, hc⟩ := ae_eq_const_of_keepsRealZeros hRH hg'm hg'b hkeep
    have hw0 : ∫ x, w x ∂thetaSourceMeasure = 0 := by
      have := hw.2
      simpa [LinearMap.mem_ker, thetaMeanL1_apply] using this
    have hcw : ∫ x, g' x * w x ∂thetaSourceMeasure = ∫ x, c * w x ∂thetaSourceMeasure :=
      integral_congr_ae (hc.mono fun x hx => by simp only [hx])
    rw [hrep w hw.1, hcw, integral_const_mul, hw0, mul_zero]
  · intro hcl
    by_contra hRH
    push Not at hRH
    obtain ⟨z, hz, him⟩ := hRH
    obtain ⟨α, hα, -⟩ := exists_mem_xiQuadrantZeros hz him
    obtain ⟨g, hgc, hge, ⟨C, hgb⟩, hann, hpos⟩ := exists_offLine_annihilator hα
    have hgL := toLp_of_bounded hgc hgb
    have hmean : ∫ x, g x ∂thetaSourceMeasure = 0 := by
      have h1 := hann thetaOneL1 (Submodule.subset_span (Set.mem_insert _ _))
      rwa [integral_mul_thetaOneL1, ← integral_thetaSourceMeasure] at h1
    have hmem : hgL.toLp g ∈ thetaJetSpan.topologicalClosure := by
      rw [hcl]
      refine ⟨toLp_mem_thetaEvenL1 hgL hge, ?_⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        thetaMeanL1_apply]
      rw [integral_congr_ae (MemLp.coeFn_toLp hgL)]
      exact hmean
    have hannV : ∀ s ∈ thetaJetSpan, ∫ x, g x * s x ∂thetaSourceMeasure = 0 := fun s hs =>
      hann s (Submodule.span_mono (Set.subset_insert _ _) hs)
    have h := (GaloisForLFunctions.HTGeometry.mem_topologicalClosure_iff_linfty.1 hmem) g
      hgc.stronglyMeasurable ⟨C, ae_of_all _ hgb⟩ hannV
    rw [integral_mul_toLp] at h
    linarith

end

end RHTower
