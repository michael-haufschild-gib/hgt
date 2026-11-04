import GaloisForLFunctions.ZeroConfigurationGeometry.TheCurveCameraIdentifiesAtTheGenus

/-!
# Bounded images certify purity

Certification in the function-field model. The camera of the curve model records the eigenvalue
power sums `S_m = Σ_z z^m` over the eigenvalue configuration `E = {r(t), r(t)⁻¹ : t ∈ T}` of the
trace points (`eigenConfig`, `curveImage_eq_powerSum_eigenConfig`). The tilt of an eigenvalue is
its modulus; purity is modulus one throughout.

* **Simultaneous return** (`exists_simultaneous_return`). Finitely many unimodular numbers return
  together near `1` at arbitrarily large exponents: the orbit `n ↦ (u^n)_u` lies in a compact
  torus, so a subsequence converges and differences of its exponents bring every `u^n` near `1`.
* **The image grows like the deepest eigenvalue** (`exists_large_powerSum`, `curveImage_growth`).
  If `R > 0` is the largest modulus in a finite configuration, the power sums obey `|S_n| ≤ |E| R^n`
  for all `n` and `|S_n| ≥ R^n/4` for arbitrarily large `n`: the top layer returns near its
  multiplicity, and the lower layers decay relative to `R^n`. The growth exponent of the image is
  the deepest tilt.
* **The Weil bound** (`norm_curveImage_le_of_isPure`). A pure trace polynomial has
  `|S_m| ≤ 2 deg Q` at every order.
* **Bounded images certify purity** (`isPure_iff_bounded_curveImage`). A trace polynomial is pure
  iff its image is bounded over all orders: an eigenvalue of modulus `> 1` forces unbounded growth,
  and the pairing `z ↔ z⁻¹` then puts every eigenvalue on the unit circle.

With `TheCurveCameraIdentifiesAtTheGenus` this gives the two certificates of the model: the exact
image up to the genus, or a size bound at all orders. A size bound at finitely many orders is not
a certificate, since tilted mimics agree with any configuration below the genus.
-/

open Polynomial Filter Topology

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-! ### Return and growth of power sums -/

/-- **Simultaneous return.** For a finite multiset `U` of unimodular numbers and every `m₀`, some
`n ≥ m₀` has `|u^n − 1| < 1/2` for all `u ∈ U`. -/
theorem exists_simultaneous_return (U : Multiset ℂ) (hU : ∀ u ∈ U, ‖u‖ = 1) (m₀ : ℕ) :
    ∃ n, m₀ ≤ n ∧ ∀ u ∈ U, ‖u ^ n - 1‖ < 1 / 2 := by
  classical
  let x : ℕ → (U.toFinset → ℂ) := fun m i => (i : ℂ) ^ m
  have hS : IsCompact (Set.pi Set.univ fun _ : U.toFinset => Metric.sphere (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_sphere 0 1
  have hx : ∀ m, x m ∈ Set.pi Set.univ fun _ : U.toFinset => Metric.sphere (0 : ℂ) 1 := by
    intro m i _
    rw [Metric.mem_sphere, dist_zero_right, norm_pow, hU _ (Multiset.mem_toFinset.mp i.2), one_pow]
  obtain ⟨a, _, φ, hφ, hlim⟩ := hS.tendsto_subseq hx
  obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.mp hlim (1 / 4) (by norm_num)
  have hgap : ∀ j, φ k₀ + j ≤ φ (k₀ + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => have := hφ (show k₀ + j < k₀ + (j + 1) by omega); omega
  refine ⟨φ (k₀ + m₀) - φ k₀, by have := hgap m₀; omega, fun u hu => ?_⟩
  set i : U.toFinset := ⟨u, Multiset.mem_toFinset.mpr hu⟩
  have h1 := hk₀ (k₀ + m₀) (by omega)
  have h2 := hk₀ k₀ le_rfl
  rw [dist_eq_norm] at h1 h2
  have c1 : ‖u ^ φ (k₀ + m₀) - a i‖ < 1 / 4 :=
    lt_of_le_of_lt (norm_le_pi_norm ((x ∘ φ) (k₀ + m₀) - a) i) h1
  have c2 : ‖u ^ φ k₀ - a i‖ < 1 / 4 := lt_of_le_of_lt (norm_le_pi_norm ((x ∘ φ) k₀ - a) i) h2
  have hsplit : u ^ φ (k₀ + m₀) = u ^ φ k₀ * u ^ (φ (k₀ + m₀) - φ k₀) := by
    rw [← pow_add, Nat.add_sub_cancel' (hφ.monotone (by omega))]
  have hnorm : ‖u ^ φ k₀‖ = 1 := by rw [norm_pow, hU u hu, one_pow]
  calc ‖u ^ (φ (k₀ + m₀) - φ k₀) - 1‖
      = ‖u ^ φ k₀ * (u ^ (φ (k₀ + m₀) - φ k₀) - 1)‖ := by rw [norm_mul, hnorm, one_mul]
    _ = ‖(u ^ φ (k₀ + m₀) - a i) - (u ^ φ k₀ - a i)‖ := by rw [hsplit]; congr 1; ring
    _ ≤ ‖u ^ φ (k₀ + m₀) - a i‖ + ‖u ^ φ k₀ - a i‖ := norm_sub_le _ _
    _ < 1 / 2 := by linarith

theorem re_sum_ge_of_near_one (U : Multiset ℂ) (f : ℂ → ℂ) (h : ∀ u ∈ U, ‖f u - 1‖ < 1 / 2) :
    (Multiset.card U : ℝ) / 2 ≤ ((U.map f).sum).re := by
  induction U using Multiset.induction_on with
  | empty => simp
  | cons a U ih =>
    have ha := h a (Multiset.mem_cons_self a U)
    have hU := ih fun u hu => h u (Multiset.mem_cons_of_mem hu)
    have hre : |(f a - 1).re| ≤ ‖f a - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at hre
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, Complex.add_re,
      Nat.cast_add, Nat.cast_one]
    linarith [neg_abs_le ((f a).re - 1)]

theorem norm_sum_map_le (T : Multiset ℂ) (f : ℂ → ℂ) {B : ℝ} (h : ∀ t ∈ T, ‖f t‖ ≤ B) :
    ‖(T.map f).sum‖ ≤ Multiset.card T * B := by
  induction T using Multiset.induction_on with
  | empty => simp
  | cons a T ih =>
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add, Nat.cast_one]
    have := ih fun t ht => h t (Multiset.mem_cons_of_mem ht)
    linarith [norm_add_le (f a) (T.map f).sum, h a (Multiset.mem_cons_self a T)]

/-- **Power sums grow like the largest modulus.** If every `w ∈ W` has `|w| ≤ R` and some has
`|w| = R > 0`, then `|Σ_w w^n| ≥ R^n/4` for arbitrarily large `n`. -/
theorem exists_large_powerSum (W : Multiset ℂ) {R : ℝ} (hR : 0 < R) (hmax : ∀ w ∈ W, ‖w‖ ≤ R)
    (hatt : ∃ w ∈ W, ‖w‖ = R) (m₀ : ℕ) :
    ∃ n, m₀ ≤ n ∧ R ^ n / 4 ≤ ‖(W.map fun w => w ^ n).sum‖ := by
  classical
  set U := W.filter fun w => ‖w‖ = R with hU
  set V := W.filter fun w => ¬ ‖w‖ = R with hV
  have hWUV : U + V = W := Multiset.filter_add_not _ W
  -- the modulus of the lower layer
  obtain ⟨R', hR'0, hR'R, hVR'⟩ : ∃ R', 0 ≤ R' ∧ R' < R ∧ ∀ v ∈ V, ‖v‖ ≤ R' := by
    rcases V.toFinset.eq_empty_or_nonempty with h | h
    · refine ⟨0, le_rfl, hR, fun v hv => ?_⟩
      have := Multiset.mem_toFinset.mpr hv
      rw [h] at this
      simp at this
    · obtain ⟨v₀, hv₀, hmaxv⟩ := V.toFinset.exists_max_image (fun v => ‖v‖) h
      have hv₀' := Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hv₀)
      exact ⟨‖v₀‖, norm_nonneg _, lt_of_le_of_ne (hmax v₀ hv₀'.1) hv₀'.2,
        fun v hv => hmaxv v (Multiset.mem_toFinset.mpr hv)⟩
  -- eventually the lower layer is below `R^n/4`
  have hratio : Tendsto (fun n : ℕ => (Multiset.card V : ℝ) * (R' / R) ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR'0 hR.le)
      ((div_lt_one hR).mpr hR'R)).const_mul (Multiset.card V : ℝ)
    rwa [mul_zero] at this
  obtain ⟨N, hN⟩ :=
    eventually_atTop.mp (hratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  -- the top layer returns near its multiplicity
  have hunit : ∀ u ∈ U.map (fun u : ℂ => u / (R : ℂ)), ‖u‖ = 1 := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hu
    have hwR : ‖w‖ = R := (Multiset.mem_filter.mp hw).2
    rw [norm_div, hwR, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne']
  obtain ⟨n, hn, hret⟩ := exists_simultaneous_return _ hunit (max m₀ N)
  refine ⟨n, (le_max_left _ _).trans hn, ?_⟩
  have hRn : 0 < R ^ n := pow_pos hR n
  have hUn : (U.map fun w => w ^ n).sum =
      (R : ℂ) ^ n * (U.map fun u : ℂ => (u / (R : ℂ)) ^ n).sum := by
    rw [← Multiset.sum_map_mul_left]
    refine congrArg _ (Multiset.map_congr rfl fun u _ => ?_)
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hR.ne'))]
  have hUlow : (1 : ℝ) / 2 ≤ ‖(U.map fun u : ℂ => (u / (R : ℂ)) ^ n).sum‖ := by
    have hcard : (1 : ℝ) ≤ Multiset.card U := by
      obtain ⟨w, hw, hwR⟩ := hatt
      exact_mod_cast Multiset.card_pos_iff_exists_mem.mpr ⟨w, Multiset.mem_filter.mpr ⟨hw, hwR⟩⟩
    have := re_sum_ge_of_near_one U (fun u : ℂ => (u / (R : ℂ)) ^ n)
      fun u hu => hret _ (Multiset.mem_map_of_mem _ hu)
    linarith [Complex.re_le_norm ((U.map fun u : ℂ => (u / (R : ℂ)) ^ n).sum)]
  have hU' : R ^ n / 2 ≤ ‖(U.map fun w => w ^ n).sum‖ := by
    rw [hUn, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    nlinarith
  have hVn : ‖(V.map fun w => w ^ n).sum‖ ≤ Multiset.card V * R' ^ n :=
    norm_sum_map_le V _ fun v hv => by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hVR' v hv) n
  have hVsmall : (Multiset.card V : ℝ) * R' ^ n ≤ R ^ n / 4 := by
    have hNn := hN n ((le_max_right _ _).trans hn)
    rw [div_pow] at hNn
    have e : (Multiset.card V : ℝ) * R' ^ n = (Multiset.card V * (R' ^ n / R ^ n)) * R ^ n := by
      rw [mul_assoc, div_mul_cancel₀ _ hRn.ne']
    rw [e]
    have := mul_lt_mul_of_pos_right hNn hRn
    linarith
  have htri := norm_sub_norm_le ((U.map fun w => w ^ n).sum) (-(V.map fun w => w ^ n).sum)
  rw [sub_neg_eq_add, norm_neg] at htri
  rw [← hWUV, Multiset.map_add, Multiset.sum_add]
  linarith

/-! ### The eigenvalue configuration -/

/-- A chosen eigenvalue over a trace point: `r(t) + r(t)⁻¹ = t`. -/
def eigenRoot (t : ℂ) : ℂ := (exists_add_inv_eq t).choose

theorem eigenRoot_ne_zero (t : ℂ) : eigenRoot t ≠ 0 := (exists_add_inv_eq t).choose_spec.1

theorem eigenRoot_add_inv (t : ℂ) : eigenRoot t + (eigenRoot t)⁻¹ = t :=
  (exists_add_inv_eq t).choose_spec.2

/-- The eigenvalue configuration `{r(t), r(t)⁻¹ : t ∈ T}` of a trace configuration. -/
def eigenConfig (T : Multiset ℂ) : Multiset ℂ := T.bind fun t => {eigenRoot t, (eigenRoot t)⁻¹}

theorem curveImage_eq_powerSum_eigenConfig (T : Multiset ℂ) (m : ℕ) :
    curveImage T m = ((eigenConfig T).map fun z => z ^ m).sum := by
  rw [curveImage_eq_sum_eigenvalues T eigenRoot
      (fun t _ => ⟨eigenRoot_ne_zero t, eigenRoot_add_inv t⟩) m,
    eigenConfig, Multiset.map_bind, Multiset.sum_bind]
  simp

theorem card_eigenConfig (T : Multiset ℂ) :
    Multiset.card (eigenConfig T) = 2 * Multiset.card T := by
  rw [eigenConfig, Multiset.card_bind]
  simp [mul_comm]

theorem mem_traceConfig {Q : ℝ[X]} (hQ : Q ≠ 0) {z : ℂ} :
    z ∈ traceConfig Q ↔ (aeval z Q : ℂ) = 0 := by
  rw [traceConfig, mem_roots_map_of_injective (algebraMap ℝ ℂ).injective hQ, aeval_def]

/-! ### Certification by size -/

/-- **The Weil bound.** A pure trace polynomial has `|S_m| ≤ 2 deg Q` at every order. -/
theorem norm_curveImage_le_of_isPure {Q : ℝ[X]} (hQ : Q ≠ 0) (hpure : IsPure Q) (m : ℕ) :
    ‖curveImage (traceConfig Q) m‖ ≤ 2 * Q.natDegree := by
  rw [curveImage_eq_sum_eigenvalues _ eigenRoot
    (fun t _ => ⟨eigenRoot_ne_zero t, eigenRoot_add_inv t⟩) m, ← card_traceConfig]
  refine (norm_sum_map_le _ _ fun t ht => ?_).trans_eq (mul_comm _ _)
  obtain ⟨him, hre⟩ := (isPure_iff_complex hQ).mp hpure t ((mem_traceConfig hQ).mp ht)
  have hr : ‖eigenRoot t‖ = 1 := norm_eq_one_of_add_inv (eigenRoot_ne_zero t)
    ((eigenRoot_add_inv t).trans (Complex.ext (by simp) (by simp [him]))) hre
  calc ‖eigenRoot t ^ m + (eigenRoot t)⁻¹ ^ m‖
      ≤ ‖eigenRoot t ^ m‖ + ‖(eigenRoot t)⁻¹ ^ m‖ := norm_add_le _ _
    _ = 2 := by rw [norm_pow, norm_pow, norm_inv, hr]; norm_num

/-- **The image grows like the deepest eigenvalue.** If `z₀` has the largest modulus in the
eigenvalue configuration, then `|S_n| ≤ 2 deg Q · |z₀|^n` for all `n`, and `|S_n| ≥ |z₀|^n/4` for
arbitrarily large `n`. -/
theorem curveImage_growth {Q : ℝ[X]} {z₀ : ℂ}
    (hz₀ : z₀ ∈ eigenConfig (traceConfig Q))
    (hmax : ∀ z ∈ eigenConfig (traceConfig Q), ‖z‖ ≤ ‖z₀‖) :
    (∀ n, ‖curveImage (traceConfig Q) n‖ ≤ 2 * Q.natDegree * ‖z₀‖ ^ n) ∧
      ∀ m₀, ∃ n, m₀ ≤ n ∧ ‖z₀‖ ^ n / 4 ≤ ‖curveImage (traceConfig Q) n‖ := by
  have hz₀0 : z₀ ≠ 0 := by
    obtain ⟨t, _, ht⟩ := Multiset.mem_bind.mp hz₀
    rcases Multiset.mem_cons.mp ht with h | h
    · rw [h]; exact eigenRoot_ne_zero t
    · rw [Multiset.mem_singleton.mp h]; exact inv_ne_zero (eigenRoot_ne_zero t)
  refine ⟨fun n => ?_, fun m₀ => ?_⟩
  · rw [curveImage_eq_powerSum_eigenConfig]
    refine (norm_sum_map_le (B := ‖z₀‖ ^ n) _ _ fun z hz => ?_).trans_eq ?_
    · exact (norm_pow z n).trans_le (pow_le_pow_left₀ (norm_nonneg _) (hmax z hz) n)
    · rw [card_eigenConfig, card_traceConfig]; push_cast; ring
  · rw [funext fun n => curveImage_eq_powerSum_eigenConfig (traceConfig Q) n]
    exact exists_large_powerSum _ (norm_pos_iff.mpr hz₀0) hmax ⟨z₀, hz₀, rfl⟩ m₀

/-- **Bounded images certify purity.** A nonzero trace polynomial is pure iff its curve image is
bounded over all orders. -/
theorem isPure_iff_bounded_curveImage {Q : ℝ[X]} (hQ : Q ≠ 0) :
    IsPure Q ↔ ∃ C, ∀ m, ‖curveImage (traceConfig Q) m‖ ≤ C := by
  refine ⟨fun h => ⟨_, norm_curveImage_le_of_isPure hQ h⟩, fun ⟨C, hC⟩ => ?_⟩
  classical
  set E := eigenConfig (traceConfig Q) with hE
  -- an eigenvalue of modulus `> 1` would make the image unbounded
  have hle : ∀ z ∈ E, ‖z‖ ≤ 1 := by
    intro z₁ hz₁
    by_contra hz₁1
    have hne : E.toFinset.Nonempty := ⟨z₁, Multiset.mem_toFinset.mpr hz₁⟩
    obtain ⟨z₀, hz₀, hmax⟩ := E.toFinset.exists_max_image (fun z => ‖z‖) hne
    have hR1 : 1 < ‖z₀‖ :=
      (not_le.mp hz₁1).trans_le (hmax z₁ (Multiset.mem_toFinset.mpr hz₁))
    obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt (4 * C) hR1
    obtain ⟨n, hn, hbig⟩ := exists_large_powerSum E (by linarith)
      (fun w hw => hmax w (Multiset.mem_toFinset.mpr hw)) ⟨z₀, Multiset.mem_toFinset.mp hz₀, rfl⟩ m₀
    have h1 := hC n
    rw [curveImage_eq_powerSum_eigenConfig] at h1
    have h2 : ‖z₀‖ ^ m₀ ≤ ‖z₀‖ ^ n := pow_le_pow_right₀ hR1.le hn
    linarith
  -- the pairing `z ↔ z⁻¹` puts every eigenvalue on the circle
  rw [isPure_iff_complex hQ]
  intro t ht
  have htT : t ∈ traceConfig Q := (mem_traceConfig hQ).mpr ht
  have hr1 : ‖eigenRoot t‖ ≤ 1 := hle _ (Multiset.mem_bind.mpr ⟨t, htT, by simp⟩)
  have hr2 : ‖(eigenRoot t)⁻¹‖ ≤ 1 := hle _ (Multiset.mem_bind.mpr ⟨t, htT, by simp⟩)
  have hpos : 0 < ‖eigenRoot t‖ := norm_pos_iff.mpr (eigenRoot_ne_zero t)
  rw [norm_inv, inv_le_one₀ hpos] at hr2
  obtain ⟨h1, h2⟩ := add_inv_of_norm_eq_one (le_antisymm hr1 hr2)
  rw [eigenRoot_add_inv] at h1
  rw [h1]
  simpa using h2

end GaloisForLFunctions.ZeroConfigurationGeometry
