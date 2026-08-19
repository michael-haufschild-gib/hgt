import Mathlib
import GaloisForLFunctions.HTGeometry.KreinLangerInertia
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn

/-!
# The normalized remote conjugate-pair gauge and its escape to infinity

`faithful-krein-index-escape-stratification`, equation `(2)`.

For an upper-half-plane point `t`, the normalized factor

```text
A_t(z) = (z - t)(z - conj t) / |t|²
```

is a real (Schwarz-symmetric) quadratic polynomial with `A_t(0) = 1`, whose negative logarithmic
derivative is the one-pair Krein carrier `1/(t - z) + 1/(conj t - z)`.  If the real part of `t`
stays bounded while `|t| → ∞`, then `A_t → 1` locally uniformly together with every derivative,
so the inserted conjugate pair escapes to spectral infinity without moving the carrier in the
compact-open topology.

The finite product `remotePairGauge t = ∏_q A_{t q}` is the gauge `A_(r,T)` of the card.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The gauge -/

/-- One normalized remote conjugate-pair factor `((z - t)(z - conj t))/|t|²`. -/
def remotePairFactor (t z : ℂ) : ℂ :=
  (z - t) * (z - (starRingEnd ℂ) t) / (Complex.normSq t : ℂ)

/-- The normalized remote conjugate-pair gauge `A_(r,T)`. -/
def remotePairGauge {r : ℕ} (t : Fin r → ℂ) (z : ℂ) : ℂ :=
  ∏ q, remotePairFactor (t q) z

theorem normSq_ne_zero_of_ne_zero {t : ℂ} (ht : t ≠ 0) : (Complex.normSq t : ℂ) ≠ 0 := by
  have h : Complex.normSq t ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using ht
  exact_mod_cast h

/-- The explicit quadratic form of the factor. -/
theorem remotePairFactor_eq {t : ℂ} (ht : t ≠ 0) (z : ℂ) :
    remotePairFactor t z
      = 1 + (z ^ 2 - 2 * (t.re : ℂ) * z) * ((Complex.normSq t : ℂ))⁻¹ := by
  have hns : (Complex.normSq t : ℂ) ≠ 0 := normSq_ne_zero_of_ne_zero ht
  have hexp : (z - t) * (z - (starRingEnd ℂ) t)
      = z ^ 2 - 2 * (t.re : ℂ) * z + (Complex.normSq t : ℂ) := by
    have hadd : t + (starRingEnd ℂ) t = 2 * (t.re : ℂ) := by
      rw [Complex.add_conj]; push_cast; ring
    have hmul : t * (starRingEnd ℂ) t = (Complex.normSq t : ℂ) := Complex.mul_conj t
    have : (z - t) * (z - (starRingEnd ℂ) t)
        = z ^ 2 - (t + (starRingEnd ℂ) t) * z + t * (starRingEnd ℂ) t := by ring
    rw [this, hadd, hmul]
  rw [remotePairFactor, hexp]
  field_simp
  ring

/-- The factor is a Schwarz-real polynomial. -/
theorem remotePairFactor_conj (t z : ℂ) :
    (starRingEnd ℂ) (remotePairFactor t ((starRingEnd ℂ) z)) = remotePairFactor t z := by
  simp only [remotePairFactor, map_div₀, map_mul, map_sub, Complex.conj_conj,
    Complex.conj_ofReal]
  ring_nf

theorem remotePairGauge_conj {r : ℕ} (t : Fin r → ℂ) (z : ℂ) :
    (starRingEnd ℂ) (remotePairGauge t ((starRingEnd ℂ) z)) = remotePairGauge t z := by
  rw [remotePairGauge, remotePairGauge, map_prod]
  exact Finset.prod_congr rfl fun q _ => remotePairFactor_conj (t q) z

theorem differentiable_remotePairFactor (t : ℂ) : Differentiable ℂ (remotePairFactor t) := by
  unfold remotePairFactor
  fun_prop

theorem remotePairGauge_eq_prod {r : ℕ} (t : Fin r → ℂ) :
    remotePairGauge t = ∏ q : Fin r, remotePairFactor (t q) := by
  funext w
  simp [remotePairGauge, Finset.prod_apply]

theorem differentiable_remotePairGauge {r : ℕ} (t : Fin r → ℂ) :
    Differentiable ℂ (remotePairGauge t) := by
  rw [remotePairGauge_eq_prod]
  exact Differentiable.finsetProd fun q _ => differentiable_remotePairFactor (t q)

/-- The zeros of the factor are exactly the inserted conjugate pair. -/
theorem remotePairFactor_eq_zero_iff {t : ℂ} (ht : t ≠ 0) (z : ℂ) :
    remotePairFactor t z = 0 ↔ z = t ∨ z = (starRingEnd ℂ) t := by
  have hns : (Complex.normSq t : ℂ) ≠ 0 := normSq_ne_zero_of_ne_zero ht
  rw [remotePairFactor, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h1 | h1
      · exact Or.inl (by linear_combination h1)
      · exact Or.inr (by linear_combination h1)
    · exact absurd h hns
  · rintro (rfl | rfl)
    · left; simp
    · left; simp

theorem remotePairGauge_ne_zero {r : ℕ} {t : Fin r → ℂ} (ht : ∀ q, t q ≠ 0) {z : ℂ}
    (hz : ∀ q, z ≠ t q ∧ z ≠ (starRingEnd ℂ) (t q)) : remotePairGauge t z ≠ 0 := by
  rw [remotePairGauge]
  refine Finset.prod_ne_zero_iff.mpr fun q _ => ?_
  intro h
  rcases (remotePairFactor_eq_zero_iff (ht q) z).mp h with h1 | h1
  · exact (hz q).1 h1
  · exact (hz q).2 h1

/-! ## The negative logarithmic derivative is the Krein pair carrier -/

theorem logDeriv_remotePairFactor {t z : ℂ} (ht : t ≠ 0)
    (hz1 : z ≠ t) (hz2 : z ≠ (starRingEnd ℂ) t) :
    logDeriv (remotePairFactor t) z = (z - t)⁻¹ + (z - (starRingEnd ℂ) t)⁻¹ := by
  have hns : (Complex.normSq t : ℂ) ≠ 0 := normSq_ne_zero_of_ne_zero ht
  have h1 : z - t ≠ 0 := sub_ne_zero.mpr hz1
  have h2 : z - (starRingEnd ℂ) t ≠ 0 := sub_ne_zero.mpr hz2
  have hfun : remotePairFactor t
      = fun w => ((w - t) * (w - (starRingEnd ℂ) t)) * ((Complex.normSq t : ℂ))⁻¹ := by
    funext w
    rw [remotePairFactor, div_eq_mul_inv]
  have hd1 : HasDerivAt (fun w : ℂ => w - t) 1 z := by
    simpa using (hasDerivAt_id z).sub_const t
  have hd2 : HasDerivAt (fun w : ℂ => w - (starRingEnd ℂ) t) 1 z := by
    simpa using (hasDerivAt_id z).sub_const ((starRingEnd ℂ) t)
  have hprod : HasDerivAt (fun w : ℂ => (w - t) * (w - (starRingEnd ℂ) t))
      (1 * (z - (starRingEnd ℂ) t) + (z - t) * 1) z := hd1.mul hd2
  have hscaled : HasDerivAt (remotePairFactor t)
      ((1 * (z - (starRingEnd ℂ) t) + (z - t) * 1) * ((Complex.normSq t : ℂ))⁻¹) z := by
    rw [hfun]
    exact hprod.mul_const _
  rw [logDeriv_apply, hscaled.deriv, remotePairFactor, div_eq_mul_inv]
  field_simp

theorem logDeriv_remotePairGauge {r : ℕ} {t : Fin r → ℂ} (ht : ∀ q, t q ≠ 0) {z : ℂ}
    (hz : ∀ q, z ≠ t q ∧ z ≠ (starRingEnd ℂ) (t q)) :
    logDeriv (remotePairGauge t) z
      = ∑ q, ((z - t q)⁻¹ + (z - (starRingEnd ℂ) (t q))⁻¹) := by
  have hne : ∀ q ∈ Finset.univ, remotePairFactor (t q) z ≠ 0 := by
    intro q _
    intro h
    rcases (remotePairFactor_eq_zero_iff (ht q) z).mp h with h1 | h1
    · exact (hz q).1 h1
    · exact (hz q).2 h1
  have hdiff : ∀ q ∈ Finset.univ, DifferentiableAt ℂ (remotePairFactor (t q)) z :=
    fun q _ => (differentiable_remotePairFactor (t q)) z
  have hfun : remotePairGauge t = fun w => ∏ q : Fin r, remotePairFactor (t q) w := rfl
  rw [hfun, logDeriv_prod hne hdiff]
  exact Finset.sum_congr rfl fun q _ => logDeriv_remotePairFactor (ht q) (hz q).1 (hz q).2

/-- **The gauge's negative logarithmic derivative is the Krein multi-pair carrier.** -/
theorem neg_logDeriv_remotePairGauge {r : ℕ} {t : Fin r → ℂ} (ht : ∀ q, t q ≠ 0) {z : ℂ}
    (hz : ∀ q, z ≠ t q ∧ z ≠ (starRingEnd ℂ) (t q)) :
    -logDeriv (remotePairGauge t) z = multiPairCarrier t z := by
  have hterm : ∀ q : Fin r, (t q - z)⁻¹ + (star (t q) - z)⁻¹
      = -((z - t q)⁻¹ + (z - (starRingEnd ℂ) (t q))⁻¹) := by
    intro q
    have h1 : t q - z = -(z - t q) := by ring
    have h2 : star (t q) - z = -(z - (starRingEnd ℂ) (t q)) := by
      rw [Complex.star_def]; ring
    rw [h1, h2, inv_neg, inv_neg]
    ring
  rw [logDeriv_remotePairGauge ht hz, multiPairCarrier]
  simp only [hterm, Finset.sum_neg_distrib]

/-! ## Escape to spectral infinity -/

theorem tendstoLocallyUniformly_const_seq {ι α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {l : Filter ι} (f : α → β) : TendstoLocallyUniformly (fun _ : ι => f) f l := by
  intro u hu x
  exact ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩

/-- Locally uniform convergence passes through a finite product. -/
theorem tendstoLocallyUniformly_finset_prod {ι κ : Type*} {l : Filter ι} (s : Finset κ)
    (f : κ → ι → ℂ → ℂ) (g : κ → ℂ → ℂ)
    (hf : ∀ k ∈ s, TendstoLocallyUniformly (f k) (g k) l)
    (hg : ∀ k ∈ s, Continuous (g k)) :
    TendstoLocallyUniformly (fun i z => ∏ k ∈ s, f k i z) (fun z => ∏ k ∈ s, g k z) l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        tendstoLocallyUniformly_const_seq (ι := ι) (l := l) (fun _ : ℂ => (1 : ℂ))
  | insert k s hk ih =>
      have hfk : TendstoLocallyUniformly (f k) (g k) l := hf k (Finset.mem_insert_self k s)
      have hgk : Continuous (g k) := hg k (Finset.mem_insert_self k s)
      have hrest := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hg j (Finset.mem_insert_of_mem hj))
      have hgrest : Continuous (fun z => ∏ j ∈ s, g j z) := by
        exact continuous_finsetProd s fun j hj => hg j (Finset.mem_insert_of_mem hj)
      have hmul := hfk.mul₀ hrest hgk hgrest
      have hshape : (fun i z => ∏ j ∈ insert k s, f j i z)
          = fun i z => f k i z * ∏ j ∈ s, f j i z := by
        funext i z
        rw [Finset.prod_insert hk]
      have hshape' : (fun z => ∏ j ∈ insert k s, g j z)
          = fun z => g k z * ∏ j ∈ s, g j z := by
        funext z
        rw [Finset.prod_insert hk]
      rw [hshape, hshape']
      exact hmul

/-- A coefficient tending to zero times a fixed continuous shape gives locally uniform
convergence to one. -/
theorem tendstoLocallyUniformly_one_add_mul {ι : Type*} {l : Filter ι} (c : ι → ℂ) (g : ℂ → ℂ)
    (hg : Continuous g) (hc : Tendsto c l (nhds 0)) :
    TendstoLocallyUniformly (fun i z => 1 + g z * c i) (fun _ : ℂ => (1 : ℂ)) l := by
  have hcoeff : TendstoLocallyUniformly
      (fun i (_ : ℂ) => c i) (fun _ : ℂ => (0 : ℂ)) l :=
    (hc.tendstoUniformly_const).tendstoLocallyUniformly
  have hshape : TendstoLocallyUniformly (fun (_ : ι) (z : ℂ) => g z) g l :=
    tendstoLocallyUniformly_const_seq _
  have hmul := hshape.mul₀ hcoeff hg continuous_const
  have hone : TendstoLocallyUniformly
      (fun (_ : ι) (_ : ℂ) => (1 : ℂ)) (fun _ : ℂ => (1 : ℂ)) l :=
    tendstoLocallyUniformly_const_seq _
  have hadd := hone.add hmul
  have hL : ((fun (_ : ℂ) => (1 : ℂ)) + g * (fun _ : ℂ => (0 : ℂ))) = (fun _ : ℂ => (1 : ℂ)) := by
    funext z; simp
  rw [hL] at hadd
  exact hadd

/-- **Escape of one normalized remote pair.**  If the real part of `t i` is fixed while
`|t i| → ∞`, the normalized factor tends to `1` locally uniformly. -/
theorem remotePairFactor_tendstoLocallyUniformly {ι : Type*} {l : Filter ι} {δ : ℝ}
    {t : ι → ℂ} (hre : ∀ i, (t i).re = δ) (hne : ∀ i, t i ≠ 0)
    (hnorm : Tendsto (fun i => ((Complex.normSq (t i) : ℂ))⁻¹) l (nhds 0)) :
    TendstoLocallyUniformly (fun i z => remotePairFactor (t i) z) (fun _ : ℂ => (1 : ℂ)) l := by
  have hbase := tendstoLocallyUniformly_one_add_mul (l := l)
    (fun i => ((Complex.normSq (t i) : ℂ))⁻¹) (fun z : ℂ => z ^ 2 - 2 * (δ : ℂ) * z)
    (by fun_prop) hnorm
  have hlhs : (fun i z => remotePairFactor (t i) z)
      = fun i (z : ℂ) => (1 : ℂ) + (z ^ 2 - 2 * (δ : ℂ) * z) * ((Complex.normSq (t i) : ℂ))⁻¹ := by
    funext i z
    rw [remotePairFactor_eq (hne i) z, hre i]
  rw [hlhs]
  exact hbase

/-- **Escape of the whole gauge.** -/
theorem remotePairGauge_tendstoLocallyUniformly {r : ℕ} {ι : Type*} {l : Filter ι}
    {δ : Fin r → ℝ} {t : ι → Fin r → ℂ}
    (hre : ∀ i q, (t i q).re = δ q) (hne : ∀ i q, t i q ≠ 0)
    (hnorm : ∀ q, Tendsto (fun i => ((Complex.normSq (t i q) : ℂ))⁻¹) l (nhds 0)) :
    TendstoLocallyUniformly (fun i z => remotePairGauge (t i) z) (fun _ : ℂ => (1 : ℂ)) l := by
  have h := tendstoLocallyUniformly_finset_prod (l := l) (Finset.univ : Finset (Fin r))
    (fun q i z => remotePairFactor (t i q) z) (fun _ (_ : ℂ) => (1 : ℂ))
    (fun q _ => remotePairFactor_tendstoLocallyUniformly (δ := δ q)
      (fun i => hre i q) (fun i => hne i q) (hnorm q))
    (fun _ _ => continuous_const)
  simpa [remotePairGauge] using h

/-- **Escape of a gauged carrier.**  Multiplying any continuous function by the escaping gauge
converges to it locally uniformly. -/
theorem remotePairGauge_mul_tendstoLocallyUniformly {r : ℕ} {ι : Type*} {l : Filter ι}
    {δ : Fin r → ℝ} {t : ι → Fin r → ℂ} {F : ℂ → ℂ} (hF : Continuous F)
    (hre : ∀ i q, (t i q).re = δ q) (hne : ∀ i q, t i q ≠ 0)
    (hnorm : ∀ q, Tendsto (fun i => ((Complex.normSq (t i q) : ℂ))⁻¹) l (nhds 0)) :
    TendstoLocallyUniformly (fun i z => remotePairGauge (t i) z * F z) F l := by
  have hgauge := remotePairGauge_tendstoLocallyUniformly hre hne hnorm
  have hFseq : TendstoLocallyUniformly (fun (_ : ι) => F) F l :=
    tendstoLocallyUniformly_const_seq _
  have hmul := hgauge.mul₀ hFseq continuous_const hF
  have hL : ((fun _ : ℂ => (1 : ℂ)) * F) = F := by funext z; simp
  rw [hL] at hmul
  exact hmul

/-- **All derivatives escape too.**  Every iterated derivative of the gauged entire carrier
converges locally uniformly to the corresponding derivative of the carrier. -/
theorem remotePairGauge_mul_iteratedDeriv_tendstoLocallyUniformly {r : ℕ} {ι : Type*}
    {l : Filter ι} {δ : Fin r → ℝ} {t : ι → Fin r → ℂ} {F : ℂ → ℂ}
    (hF : Differentiable ℂ F)
    (hre : ∀ i q, (t i q).re = δ q) (hne : ∀ i q, t i q ≠ 0)
    (hnorm : ∀ q, Tendsto (fun i => ((Complex.normSq (t i q) : ℂ))⁻¹) l (nhds 0)) (j : ℕ) :
    TendstoLocallyUniformly
      (fun i => iteratedDeriv j (fun z => remotePairGauge (t i) z * F z))
      (iteratedDeriv j F) l := by
  have hconvOn : TendstoLocallyUniformlyOn
      (fun i z => remotePairGauge (t i) z * F z) F l Set.univ := by
    simpa [tendstoLocallyUniformlyOn_univ] using
      remotePairGauge_mul_tendstoLocallyUniformly hF.continuous hre hne hnorm
  have hdiff : ∀ᶠ i in l,
      DifferentiableOn ℂ (fun z => remotePairGauge (t i) z * F z) Set.univ :=
    Filter.Eventually.of_forall fun i =>
      (((differentiable_remotePairGauge (t i)).mul hF)).differentiableOn
  have hj := iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform
    isOpen_univ hconvOn hdiff j
  simpa [tendstoLocallyUniformlyOn_univ] using hj

end GaloisForLFunctions.HTGeometry
