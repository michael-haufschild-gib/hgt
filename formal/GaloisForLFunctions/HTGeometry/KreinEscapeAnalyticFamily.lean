import GaloisForLFunctions.HTGeometry.KreinIndexEscapeStratification
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalSurgery

/-!
# The analytic escape family of the Krein-index stratification

`faithful-krein-index-escape-stratification`, equations `(2)`–`(6)`.

`movingCanonicalSurgeryProduct θ aIdx bIdx tb` is a real entire function of exact order one whose
negative logarithmic derivative is a generalized Nevanlinna carrier of exact negative index `k`.
Multiplying it by the normalized remote gauge `remotePairGauge te` gives

```text
F_(θ,k;r,T) = A_(r,T) · F_(θ,k)
```

whose negative logarithmic derivative is the same carrier plus the `r` new conjugate-pair terms.
This module proves:

* `neg_logDeriv_kreinEscapeProduct_eq` — the carrier of the gauged product;
* `kreinEscapeCarrier_exact_negativeSquares` — the index is exactly `k + r`;
* `kreinEscapeProduct_iteratedDeriv_tendstoLocallyUniformly` — as the inserted pairs escape to
  infinite height, the gauged products converge to `F_(θ,k)` with every derivative, uniformly on
  every compact set.

Together these are the escape-stratification statement `(6)`: the index-`k` stratum lies in the
compact-open closure of the index-`(k+r)` stratum, for every `k` and every `r`.
-/

open Complex Filter Topology Matrix
open scoped ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The gauged carrier: the exact index-`k` surgery carrier plus `r` further conjugate pairs. -/
def kreinEscapeCarrier {k r : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) (te : Fin r → ℂ) (z : ℂ) : ℂ :=
  movingCanonicalSurgeryCarrier θ aIdx bIdx tb z + multiPairCarrier te z

theorem kreinEscapeCarrier_eq {k r : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) (te : Fin r → ℂ) (z : ℂ) :
    kreinEscapeCarrier θ aIdx bIdx tb te z
      = escapeCarrier (movingCanonicalComplementCarrier θ
            (movingCanonicalSurgerySelectedIndices aIdx bIdx)) tb te z
        - (movingCanonicalSurgeryConstant θ aIdx bIdx : ℂ) := by
  rw [kreinEscapeCarrier, movingCanonicalSurgeryCarrier, escapeCarrier,
    multiPairCarrier_append]
  ring

theorem carrierPickMatrix_kreinEscapeCarrier {k r N : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) (te : Fin r → ℂ) (z : Fin N → ℂ) :
    carrierPickMatrix (kreinEscapeCarrier θ aIdx bIdx tb te) z
      = carrierPickMatrix (escapeCarrier (movingCanonicalComplementCarrier θ
          (movingCanonicalSurgerySelectedIndices aIdx bIdx)) tb te) z := by
  have hfun : kreinEscapeCarrier θ aIdx bIdx tb te
      = fun w => escapeCarrier (movingCanonicalComplementCarrier θ
            (movingCanonicalSurgerySelectedIndices aIdx bIdx)) tb te w
          - (movingCanonicalSurgeryConstant θ aIdx bIdx : ℂ) := by
    funext w
    exact kreinEscapeCarrier_eq θ aIdx bIdx tb te w
  rw [hfun, carrierPickMatrix_sub_real_const]

/-- **Exact index `k + r`.**  The gauged carrier has exactly `k + r` negative squares. -/
theorem kreinEscapeCarrier_exact_negativeSquares
    {k r : ℕ} (θ : BoundedRealSequence) (aIdx bIdx : Fin k → ℕ)
    (tb : Fin k → ℂ) (te : Fin r → ℂ)
    (ht : ∀ i, 0 < (Fin.append tb te i).im)
    (htinj : Function.Injective (Fin.append tb te)) :
    (∀ {N : ℕ} (z : Fin N → ℂ),
      (∀ j, 0 < (z j).im) →
      (∀ i j, z j ≠ Fin.append tb te i) →
      ∀ W : Submodule ℂ (Fin N → ℂ),
        (∀ x ∈ W, x ≠ 0 →
          (star x ⬝ᵥ (carrierPickMatrix (kreinEscapeCarrier θ aIdx bIdx tb te) z).mulVec x).re
            < 0) →
        Module.finrank ℂ W ≤ k + r) ∧
      ∃ z : Fin (k + r) → ℂ,
        (∀ j, 0 < (z j).im) ∧
        (∀ i j, z j ≠ Fin.append tb te i) ∧
        Function.Injective z ∧
        ∀ x : Fin (k + r) → ℂ, x ≠ 0 →
          (star x ⬝ᵥ (carrierPickMatrix (kreinEscapeCarrier θ aIdx bIdx tb te) z).mulVec x).re
            < 0 := by
  set S := movingCanonicalSurgerySelectedIndices aIdx bIdx with hS
  have hcore := escapeCarrier_exact_negativeSquares
    (movingCanonicalComplementCarrier θ S) tb te ht htinj
    (fun i => continuousAt_movingCanonicalComplementCarrier θ S (ht i))
    (fun {_} z hz => movingCanonicalComplementCarrier_pick_posSemidef θ S z hz)
  constructor
  · intro N z hz hzt W hW
    refine hcore.1 z hz hzt W ?_
    intro x hx hx0
    have h := hW x hx hx0
    rwa [carrierPickMatrix_kreinEscapeCarrier] at h
  · obtain ⟨z, hz, hzt, hinj, hneg⟩ := hcore.2
    refine ⟨z, hz, hzt, hinj, fun x hx => ?_⟩
    rw [carrierPickMatrix_kreinEscapeCarrier]
    exact hneg x hx

/-! ## The gauged analytic family -/

/-- The escape family `F_(θ,k;r,T) = A_(r,T) · F_(θ,k)`. -/
def kreinEscapeProduct {k r : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) (te : Fin r → ℂ) (z : ℂ) : ℂ :=
  remotePairGauge te z * movingCanonicalSurgeryProduct θ aIdx bIdx tb z

theorem differentiable_kreinEscapeProduct {k r : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) (te : Fin r → ℂ) :
    Differentiable ℂ (kreinEscapeProduct θ aIdx bIdx tb te) :=
  (differentiable_remotePairGauge te).mul
    (fun z => (movingCanonicalSurgeryProduct_analytic θ aIdx bIdx tb z
      (Set.mem_univ z)).differentiableAt)

theorem movingCanonicalSurgeryProduct_ne_zero_of_upper {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) {z : ℂ} (hz : 0 < z.im)
    (htb : ∀ i, 0 < (tb i).im) (hzb : ∀ i, z ≠ tb i) :
    movingCanonicalSurgeryProduct θ aIdx bIdx tb z ≠ 0 := by
  intro h
  rcases (movingCanonicalSurgeryProduct_eq_zero_iff θ aIdx bIdx tb z).mp h with
    ⟨n, _, hzn⟩ | ⟨i, hi | hi⟩
  · have him := congrArg Complex.im hzn
    simp only [Complex.ofReal_im] at him
    linarith
  · exact hzb i hi
  · have him := congrArg Complex.im hi
    simp only [Complex.star_def, Complex.conj_im] at him
    have := htb i
    linarith

theorem remotePairGauge_ne_zero_of_upper {r : ℕ} {te : Fin r → ℂ} (hte : ∀ q, 0 < (te q).im)
    {z : ℂ} (hz : 0 < z.im) (hze : ∀ q, z ≠ te q) : remotePairGauge te z ≠ 0 := by
  refine remotePairGauge_ne_zero (fun q => ?_) (fun q => ⟨hze q, ?_⟩)
  · intro h
    have := hte q
    rw [h] at this
    simp at this
  · intro h
    have him := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at him
    have := hte q
    linarith

/-- **The carrier of the gauged family.** -/
theorem neg_logDeriv_kreinEscapeProduct_eq {k r : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) (te : Fin r → ℂ)
    {z : ℂ} (hz : 0 < z.im) (htb : ∀ i, 0 < (tb i).im) (hte : ∀ q, 0 < (te q).im)
    (hzb : ∀ i, z ≠ tb i) (hze : ∀ q, z ≠ te q) :
    -logDeriv (kreinEscapeProduct θ aIdx bIdx tb te) z
      = kreinEscapeCarrier θ aIdx bIdx tb te z := by
  have hgne : remotePairGauge te z ≠ 0 := remotePairGauge_ne_zero_of_upper hte hz hze
  have hFne : movingCanonicalSurgeryProduct θ aIdx bIdx tb z ≠ 0 :=
    movingCanonicalSurgeryProduct_ne_zero_of_upper θ aIdx bIdx tb hz htb hzb
  have hgd : DifferentiableAt ℂ (remotePairGauge te) z := differentiable_remotePairGauge te z
  have hFd : DifferentiableAt ℂ (movingCanonicalSurgeryProduct θ aIdx bIdx tb) z :=
    (movingCanonicalSurgeryProduct_analytic θ aIdx bIdx tb z (Set.mem_univ z)).differentiableAt
  have hsplit : logDeriv (kreinEscapeProduct θ aIdx bIdx tb te) z
      = logDeriv (remotePairGauge te) z
        + logDeriv (movingCanonicalSurgeryProduct θ aIdx bIdx tb) z :=
    logDeriv_mul z hgne hFne hgd hFd
  have hgauge : -logDeriv (remotePairGauge te) z = multiPairCarrier te z := by
    refine neg_logDeriv_remotePairGauge (fun q => ?_) (fun q => ⟨hze q, ?_⟩)
    · intro h
      have := hte q
      rw [h] at this
      simp at this
    · intro h
      have him := congrArg Complex.im h
      simp only [Complex.star_def, Complex.conj_im] at him
      have := hte q
      linarith
  have hbase := neg_logDeriv_movingCanonicalSurgeryProduct_eq θ aIdx bIdx tb hz htb hzb
  rw [hsplit, neg_add, hgauge, hbase, kreinEscapeCarrier]
  ring

/-! ## Escape to infinite height -/

/-- **Equation (5).**  As the inserted conjugate pairs escape to infinite height with fixed real
parts, the gauged carriers converge to the ungauged one with every derivative, uniformly on every
compact set. -/
theorem kreinEscapeProduct_iteratedDeriv_tendstoLocallyUniformly
    {k r : ℕ} {ι : Type*} {l : Filter ι} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ)
    {δ : Fin r → ℝ} {te : ι → Fin r → ℂ}
    (hre : ∀ i q, (te i q).re = δ q) (hne : ∀ i q, te i q ≠ 0)
    (hnorm : ∀ q, Tendsto (fun i => ((Complex.normSq (te i q) : ℂ))⁻¹) l (nhds 0)) (j : ℕ) :
    TendstoLocallyUniformly
      (fun i => iteratedDeriv j (kreinEscapeProduct θ aIdx bIdx tb (te i)))
      (iteratedDeriv j (movingCanonicalSurgeryProduct θ aIdx bIdx tb)) l := by
  have hF : Differentiable ℂ (movingCanonicalSurgeryProduct θ aIdx bIdx tb) :=
    fun z => (movingCanonicalSurgeryProduct_analytic θ aIdx bIdx tb z
      (Set.mem_univ z)).differentiableAt
  exact remotePairGauge_mul_iteratedDeriv_tendstoLocallyUniformly hF hre hne hnorm j

/-! ## Order one and Schwarz reality of the gauged family -/

theorem orderOneEnvelope_remotePairFactor (t : ℂ) :
    OrderOneEnvelope (remotePairFactor t) := by
  have hbase := (orderOneEnvelope_linear_sub t).mul
    (orderOneEnvelope_linear_sub ((starRingEnd ℂ) t))
  have hconst := hbase.const_mul ((Complex.normSq t : ℂ))⁻¹
  refine hconst.congr fun z => ?_
  rw [remotePairFactor, div_eq_mul_inv]
  ring

theorem orderOneEnvelope_remotePairGauge {r : ℕ} (te : Fin r → ℂ) :
    OrderOneEnvelope (remotePairGauge te) := by
  have h := OrderOneEnvelope.finsetProd (Finset.univ : Finset (Fin r))
    (fun q => remotePairFactor (te q)) (fun q _ => orderOneEnvelope_remotePairFactor (te q))
  exact h.congr fun z => rfl

/-- **Statement 1, growth.**  The gauged family is entire of exact order one. -/
theorem kreinEscapeProduct_orderOneEnvelope {k r : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) (te : Fin r → ℂ) :
    OrderOneEnvelope (kreinEscapeProduct θ aIdx bIdx tb te) :=
  ((orderOneEnvelope_remotePairGauge te).mul
    (movingCanonicalSurgeryProduct_orderOneEnvelope θ aIdx bIdx tb)).congr fun z => rfl

theorem remotePairGauge_conj' {r : ℕ} (te : Fin r → ℂ) (z : ℂ) :
    remotePairGauge te ((starRingEnd ℂ) z) = (starRingEnd ℂ) (remotePairGauge te z) := by
  have h := remotePairGauge_conj te z
  have := congrArg (starRingEnd ℂ) h
  rwa [Complex.conj_conj] at this

/-- **Statement 1, reality.**  The gauged family is Schwarz-real. -/
theorem kreinEscapeProduct_conj {k r : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) (te : Fin r → ℂ) (z : ℂ) :
    kreinEscapeProduct θ aIdx bIdx tb te ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (kreinEscapeProduct θ aIdx bIdx tb te z) := by
  rw [kreinEscapeProduct, kreinEscapeProduct, remotePairGauge_conj',
    movingCanonicalSurgeryProduct_conj, map_mul]

theorem kreinEscapeProduct_analytic {k r : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) (te : Fin r → ℂ) :
    AnalyticOnNhd ℂ (kreinEscapeProduct θ aIdx bIdx tb te) Set.univ := by
  intro z _
  have h1 : AnalyticAt ℂ (remotePairGauge te) z :=
    ((differentiable_remotePairGauge te).differentiableOn.analyticOnNhd isOpen_univ)
      z (Set.mem_univ z)
  have h2 := movingCanonicalSurgeryProduct_analytic θ aIdx bIdx tb z (Set.mem_univ z)
  exact h1.mul h2

/-- **The zero set of the gauged family** is the base divisor together with the `r` inserted
conjugate pairs. -/
theorem kreinEscapeProduct_eq_zero_iff {k r : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ) (te : Fin r → ℂ)
    (hte : ∀ q, te q ≠ 0) (z : ℂ) :
    kreinEscapeProduct θ aIdx bIdx tb te z = 0 ↔
      ((∃ n : ℕ, n ∉ movingCanonicalSurgerySelectedIndices aIdx bIdx ∧
          z = (movingCanonicalZero θ n : ℂ)) ∨
        ∃ i : Fin k, z = tb i ∨ z = star (tb i)) ∨
      ∃ q : Fin r, z = te q ∨ z = (starRingEnd ℂ) (te q) := by
  rw [kreinEscapeProduct, mul_eq_zero, movingCanonicalSurgeryProduct_eq_zero_iff]
  constructor
  · rintro (hg | hbase)
    · right
      rw [remotePairGauge, Finset.prod_eq_zero_iff] at hg
      obtain ⟨q, _, hq⟩ := hg
      exact ⟨q, (remotePairFactor_eq_zero_iff (hte q) z).mp hq⟩
    · exact Or.inl hbase
  · rintro (hbase | ⟨q, hq⟩)
    · exact Or.inr hbase
    · left
      rw [remotePairGauge, Finset.prod_eq_zero_iff]
      exact ⟨q, Finset.mem_univ q, (remotePairFactor_eq_zero_iff (hte q) z).mpr hq⟩

/-! ## The card's concrete escape parameterization -/

/-- `t_(q,T) = δ_q + i (T + q)`: fixed real parts, imaginary parts escaping to `+∞`. -/
def kreinEscapePoint {r : ℕ} (δ : Fin r → ℝ) (T : ℝ) (q : Fin r) : ℂ :=
  (δ q : ℂ) + Complex.I * (((T + q : ℝ)) : ℂ)

@[simp] theorem kreinEscapePoint_re {r : ℕ} (δ : Fin r → ℝ) (T : ℝ) (q : Fin r) :
    (kreinEscapePoint δ T q).re = δ q := by
  simp [kreinEscapePoint]

@[simp] theorem kreinEscapePoint_im {r : ℕ} (δ : Fin r → ℝ) (T : ℝ) (q : Fin r) :
    (kreinEscapePoint δ T q).im = T + q := by
  simp [kreinEscapePoint]

theorem kreinEscapePoint_im_pos {r : ℕ} (δ : Fin r → ℝ) {T : ℝ} (hT : 0 < T) (q : Fin r) :
    0 < (kreinEscapePoint δ T q).im := by
  rw [kreinEscapePoint_im]
  have : (0 : ℝ) ≤ (q : ℕ) := Nat.cast_nonneg _
  linarith

theorem kreinEscapePoint_injective {r : ℕ} (δ : Fin r → ℝ) (T : ℝ) :
    Function.Injective (kreinEscapePoint δ T) := by
  intro p q hpq
  have him := congrArg Complex.im hpq
  rw [kreinEscapePoint_im, kreinEscapePoint_im] at him
  have hnat : ((p : ℕ) : ℝ) = ((q : ℕ) : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast hnat)

theorem kreinEscapePoint_ne_zero {r : ℕ} (δ : Fin r → ℝ) {T : ℝ} (hT : 0 < T) (q : Fin r) :
    kreinEscapePoint δ T q ≠ 0 := by
  intro h
  have him : (kreinEscapePoint δ T q).im = 0 := by rw [h]; simp
  have := kreinEscapePoint_im_pos δ hT q
  rw [him] at this
  exact lt_irrefl 0 this

theorem normSq_kreinEscapePoint {r : ℕ} (δ : Fin r → ℝ) (T : ℝ) (q : Fin r) :
    Complex.normSq (kreinEscapePoint δ T q) = (δ q) ^ 2 + (T + q) ^ 2 := by
  rw [Complex.normSq_apply, kreinEscapePoint_re, kreinEscapePoint_im]
  ring

/-- **The escape hypothesis holds for the card's parameterization.** -/
theorem tendsto_normSq_inv_kreinEscapePoint {r : ℕ} (δ : Fin r → ℝ) (q : Fin r) :
    Tendsto (fun T : ℝ => ((Complex.normSq (kreinEscapePoint δ T q) : ℂ))⁻¹) atTop (nhds 0) := by
  have hreal : Tendsto (fun T : ℝ => (δ q) ^ 2 + (T + q) ^ 2) atTop atTop := by
    have h1 : Tendsto (fun T : ℝ => (T + q) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    exact tendsto_atTop_add_const_left _ _ h1
  have hinv : Tendsto (fun T : ℝ => ((δ q) ^ 2 + (T + q) ^ 2)⁻¹) atTop (nhds 0) :=
    hreal.inv_tendsto_atTop
  have hcast : Tendsto (fun T : ℝ => ((((δ q) ^ 2 + (T + q) ^ 2)⁻¹ : ℝ) : ℂ)) atTop (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hinv
    rw [Complex.ofReal_zero] at h
    exact h
  refine hcast.congr fun T => ?_
  rw [normSq_kreinEscapePoint]
  push_cast
  ring

/-- **Equation (5) in the card's parameterization.**  As `T → ∞` the gauged carriers converge to
the ungauged one with every derivative, uniformly on every compact set. -/
theorem kreinEscapeProduct_escape_iteratedDeriv_tendstoLocallyUniformly
    {k r : ℕ} (θ : BoundedRealSequence) (aIdx bIdx : Fin k → ℕ) (tb : Fin k → ℂ)
    (δ : Fin r → ℝ) (hδ : ∀ q, δ q ≠ 0) (j : ℕ) :
    TendstoLocallyUniformly
      (fun T : ℝ =>
        iteratedDeriv j (kreinEscapeProduct θ aIdx bIdx tb (kreinEscapePoint δ T)))
      (iteratedDeriv j (movingCanonicalSurgeryProduct θ aIdx bIdx tb)) atTop := by
  refine kreinEscapeProduct_iteratedDeriv_tendstoLocallyUniformly θ aIdx bIdx tb
    (δ := δ) (fun T q => kreinEscapePoint_re δ T q) (fun T q => ?_)
    (fun q => tendsto_normSq_inv_kreinEscapePoint δ q) j
  intro h
  have hre : (kreinEscapePoint δ T q).re = δ q := kreinEscapePoint_re δ T q
  rw [h] at hre
  exact hδ q (by simpa using hre.symm)

end GaloisForLFunctions.HTGeometry
