import GaloisForLFunctions.ArithmeticInnerFunctionTheory.FarBubblesDoNotDecouple
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine
import GaloisForLFunctions.ArithmeticOrientationGeometry.EventualHasseWeilIsHasseWeil
import GaloisForLFunctions.SquareRootThreshold.AttainedDepthIsVisible
import GaloisForLFunctions.GrowingWindowsOfSpecZ.SpecZIsACurveOnEveryLattice

/-!
# The Bohr profile decomposition

A form with discrete spectrum lives on `ℓ²` of the zeros, and translation acts by the characters `e^{iγt}`. The closure of these characters in the torus is compact, and this is
the Bohr compactification of the translation group. So in the energy space translation is compact, and the only way a bounded sequence loses energy in a weak limit is by
escape to large ordinates.

* **The profile decomposition** (`exists_profile_decomposition`). A sequence of bounded energy, together with any translations, has a subsequence with a weak profile `v` and a Bohr character `χ`: the translates converge to
  `χ v` at each zero, the energy splits `E(u_k) = E(v) + E(u_k − v) + o(1)`, and the remainder tends to `0` on each finite set of zeros, for every translation.
* **Bubbles interact through characters** (`tendsto_energy_bubbles`). The energy of `Σ_j c_j τ_{t_{j,k}} a_j` converges along a subsequence to `Σ_ρ |Σ_j c_j χ_j(ρ) a_j(ρ)|²`, which is nonnegative and is not the sum of the bubble energies. The two-bubble
  defect is `2 Σ_ρ Re(ā(ρ) χ(ρ) b(ρ))` (`tendsto_energy_two_bubbles`): Lions' additive splitting is the case where this interference vanishes.
* **All on-line configurations** (`tendsto_configEnergy_bubbles`). For every tempered configuration on the line, the Weil energy of finitely many moving bubbles converges along a subsequence to the Bohr energy.
* **For `Spec ℤ`** (`riemannHypothesis_iff_orbit_relativelyCompact`, `riemannHypothesis_iff_bubbles_relativelyCompact`). RH is the relative compactness of every orbit correlation at infinity, equivalently of the Weil energy of every family of moving bubbles, with nonnegative limits.
-/

open Complex Filter Topology MeasureTheory Set
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GrowingWindowsOfSpecZ ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry Zeta23
  SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig TemperedConfig carrier_countable)

noncomputable section

/-! ### The energy space -/

/-- The energy of a spectral vector. -/
def energy {ι : Type*} (u : ι → ℂ) : ℝ := ∑' i, ‖u i‖ ^ 2

variable {ι : Type*}

theorem energy_nonneg (u : ι → ℂ) : 0 ≤ energy u := tsum_nonneg fun _ => sq_nonneg _

theorem norm_sub_sq_summable {a b : ι → ℂ} (ha : Summable fun i => ‖a i‖ ^ 2)
    (hb : Summable fun i => ‖b i‖ ^ 2) : Summable fun i => ‖a i - b i‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_) ((ha.mul_left 2).add (hb.mul_left 2))
  have h := norm_sub_le (a i) (b i)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]

/-- **Bohr extraction.** Any family of translation sequences has a subsequence along which all characters converge. -/
theorem exists_bohr_subseq [Countable ι] {J : Type*} [Countable J] (g : ι → ℝ) (t : J → ℕ → ℝ) :
    ∃ (χ : J → ι → Circle) (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∀ j i, Tendsto (fun k => Circle.exp (g i * t j (ψ k))) atTop (𝓝 (χ j i)) := by
  obtain ⟨a, ψ, hψ, ha⟩ := CompactSpace.tendsto_subseq
    (fun k : ℕ => fun p : J × ι => Circle.exp (g p.2 * t p.1 k))
  refine ⟨fun j i => a (j, i), ψ, hψ, fun j i => ?_⟩
  exact (tendsto_pi_nhds.mp ha) (j, i)

theorem tendsto_coe_exp {i : ι} {g : ι → ℝ} {t : ℕ → ℝ} {χ : Circle}
    (h : Tendsto (fun k => Circle.exp (g i * t k)) atTop (𝓝 χ)) :
    Tendsto (fun k => cexp (((g i * t k : ℝ) : ℂ) * I)) atTop (𝓝 (χ : ℂ)) := by
  have hc : Continuous fun z : Circle => (z : ℂ) := continuous_subtype_val
  have h1 := (hc.tendsto χ).comp h
  refine h1.congr fun k => ?_
  simp [Circle.coe_exp]

/-- **Bubbles interact through characters.** With unimodular `z_{j,k}(i) → χ_j(i)`, the energy of `Σ_j c_j z_{j,k} a_j`
converges to the Bohr energy. -/
theorem tendsto_energy_bubbles {n : ℕ} (c : Fin n → ℂ) {a : Fin n → ι → ℂ}
    (ha : ∀ j, Summable fun i => ‖a j i‖ ^ 2) {z : Fin n → ℕ → ι → ℂ} {χ : Fin n → ι → ℂ}
    (hz : ∀ j k i, ‖z j k i‖ = 1) (hχ : ∀ j i, Tendsto (fun k => z j k i) atTop (𝓝 (χ j i))) :
    Tendsto (fun k => energy fun i => ∑ j, c j * z j k i * a j i) atTop
      (𝓝 (energy fun i => ∑ j, c j * χ j i * a j i)) := by
  set B : ι → ℝ := fun i => (n : ℝ) * ∑ j, ‖c j‖ ^ 2 * ‖a j i‖ ^ 2 with hB
  have hBs : Summable B := (summable_sum fun j _ => (ha j).mul_left _).mul_left _
  refine tendsto_tsum_of_dominated_convergence hBs (fun i => ?_) (Eventually.of_forall fun k i => ?_)
  · have h1 : Tendsto (fun k => ∑ j, c j * z j k i * a j i) atTop (𝓝 (∑ j, c j * χ j i * a j i)) :=
      tendsto_finset_sum _ fun j _ => ((hχ j i).const_mul (c j)).mul_const (a j i)
    exact h1.norm.pow 2
  · have h1 : ‖∑ j, c j * z j k i * a j i‖ ≤ ∑ j, ‖c j‖ * ‖a j i‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
        rw [norm_mul, norm_mul, hz, mul_one])
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖c j‖ * ‖a j i‖)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc ‖∑ j, c j * z j k i * a j i‖ ^ 2 ≤ (∑ j, ‖c j‖ * ‖a j i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (n : ℝ) * ∑ j, (‖c j‖ * ‖a j i‖) ^ 2 := h2
      _ = B i := by
          simp only [hB, mul_pow]

theorem norm_add_sq' (a b : ℂ) : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (conj a * b).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_add]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **The two-bubble law.** The defect of additivity is the interference through the Bohr character. -/
theorem tendsto_energy_two_bubbles {a b : ι → ℂ} (ha : Summable fun i => ‖a i‖ ^ 2)
    (hb : Summable fun i => ‖b i‖ ^ 2) {z : ℕ → ι → ℂ} {χ : ι → ℂ} (hz : ∀ k i, ‖z k i‖ = 1)
    (hχ : ∀ i, Tendsto (fun k => z k i) atTop (𝓝 (χ i))) (hχn : ∀ i, ‖χ i‖ = 1) :
    Tendsto (fun k => energy fun i => a i + z k i * b i) atTop
      (𝓝 (energy a + energy b + 2 * ∑' i, (conj (a i) * (χ i * b i)).re)) := by
  have hs : Summable fun i => (conj (a i) * (χ i * b i)).re := by
    refine Summable.of_norm_bounded ((ha.add hb).mul_left (1 / 2)) fun i => ?_
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj, hχn, one_mul]
    nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]
  have hsum : Summable fun i => ‖a i + χ i * b i‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
      ((ha.mul_left 2).add (hb.mul_left 2))
    have h := norm_add_le (a i) (χ i * b i)
    rw [norm_mul, hχn, one_mul] at h
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]
  have hval : energy (fun i => a i + χ i * b i) =
      energy a + energy b + 2 * ∑' i, (conj (a i) * (χ i * b i)).re := by
    simp only [energy]
    rw [← tsum_mul_left, ← ha.tsum_add hb, ← (ha.add hb).tsum_add (hs.mul_left 2)]
    refine tsum_congr fun i => ?_
    rw [norm_add_sq', norm_mul, hχn, one_mul]
  rw [← hval]
  have h := tendsto_energy_bubbles (n := 2) (fun _ => (1 : ℂ)) (a := ![a, b]) (fun j => by
      fin_cases j
      · exact ha
      · exact hb) (z := ![fun _ _ => 1, z]) (χ := ![fun _ => 1, χ]) (fun j k i => by
      fin_cases j
      · simp
      · exact hz k i) (fun j i => by
      fin_cases j
      · exact tendsto_const_nhds
      · exact hχ i)
  simpa [Fin.sum_univ_two] using h

/-- The inner product of a fixed vector with a weakly null sequence tends to `0`. -/
theorem tendsto_tsum_re_zero {v : ι → ℂ} {r : ℕ → ι → ℂ} {C : ℝ} (hv : Summable fun i => ‖v i‖ ^ 2)
    (hr : ∀ k, Summable fun i => ‖r k i‖ ^ 2) (hC : ∀ k, energy (r k) ≤ C)
    (hlim : ∀ i, Tendsto (fun k => r k i) atTop (𝓝 0)) :
    Tendsto (fun k => ∑' i, (conj (v i) * r k i).re) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C' : ℝ := max C 0 + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  have hCle : ∀ k, energy (r k) ≤ C' := fun k =>
    (hC k).trans ((le_max_left _ _).trans (by rw [hC']; linarith))
  set δ : ℝ := ε / (1 + C') with hδ
  have hδpos : 0 < δ := div_pos hε (by linarith)
  obtain ⟨F, hF⟩ := eventually_atTop.mp ((tendsto_tsum_compl_atTop_zero fun i => ‖v i‖ ^ 2).eventually_lt_const
    (pow_pos hδpos 2))
  have hτ : ∑' q : {x // x ∉ F}, ‖v q‖ ^ 2 < δ ^ 2 := hF F le_rfl
  have hhead : Tendsto (fun k => ∑ i ∈ F, (conj (v i) * r k i).re) atTop (𝓝 0) := by
    have : Tendsto (fun k => ∑ i ∈ F, (conj (v i) * r k i).re) atTop
        (𝓝 (∑ i ∈ F, (conj (v i) * (0 : ℂ)).re)) :=
      tendsto_finset_sum _ fun i _ =>
        Complex.continuous_re.continuousAt.tendsto.comp ((hlim i).const_mul _)
    simpa using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hhead.eventually (Metric.ball_mem_nhds _ (half_pos hε)))
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hN k hk
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at h1
  set f : ι → ℝ := fun i => (conj (v i) * r k i).re with hf
  set b : ι → ℝ := fun i => ‖v i‖ ^ 2 / (2 * δ) + δ * ‖r k i‖ ^ 2 / 2 with hb
  have hbs : Summable b := (hv.div_const _).add (((hr k).mul_left δ).div_const 2)
  have hfb : ∀ i, |f i| ≤ b i := fun i => by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, RCLike.norm_conj]
    have e : ‖v i‖ ^ 2 / (2 * δ) + δ * ‖r k i‖ ^ 2 / 2 - ‖v i‖ * ‖r k i‖ =
        (‖v i‖ / δ - ‖r k i‖) ^ 2 * (δ / 2) := by
      field_simp
      ring
    have h0 : 0 ≤ (‖v i‖ / δ - ‖r k i‖) ^ 2 * (δ / 2) := by positivity
    simp only [hb]
    linarith
  have hfs : Summable f := Summable.of_norm_bounded hbs fun i => by
    rw [Real.norm_eq_abs]
    exact hfb i
  have hsplit : ∑ i ∈ F, f i + ∑' q : {x // x ∉ F}, f q = ∑' i, f i := hfs.sum_add_tsum_compl (s := F)
  have hsc : Summable fun q : {x // x ∉ F} => f q := hfs.subtype _
  have hbc : Summable fun q : {x // x ∉ F} => b q := hbs.subtype _
  have hvc : Summable fun q : {x // x ∉ F} => ‖v q‖ ^ 2 := hv.subtype _
  have hrc : Summable fun q : {x // x ∉ F} => ‖r k q‖ ^ 2 := (hr k).subtype _
  have htail : |∑' q : {x // x ∉ F}, f q| ≤ ∑' q : {x // x ∉ F}, b q := by
    have h2 := norm_tsum_le_tsum_norm hsc.norm
    rw [Real.norm_eq_abs] at h2
    refine h2.trans (Summable.tsum_le_tsum (fun q => ?_) hsc.norm hbc)
    rw [Real.norm_eq_abs]
    exact hfb q
  have hbt : ∑' q : {x // x ∉ F}, b q =
      (∑' q : {x // x ∉ F}, ‖v q‖ ^ 2) / (2 * δ) + δ * (∑' q : {x // x ∉ F}, ‖r k q‖ ^ 2) / 2 := by
    simp only [hb]
    rw [(hvc.div_const _).tsum_add ((hrc.mul_left δ).div_const 2), tsum_div_const, tsum_div_const,
      tsum_mul_left]
  have hrle : ∑' q : {x // x ∉ F}, ‖r k q‖ ^ 2 ≤ C' := by
    have hs : ∑ i ∈ F, ‖r k i‖ ^ 2 + ∑' q : {x // x ∉ F}, ‖r k q‖ ^ 2 = energy (r k) :=
      (hr k).sum_add_tsum_compl (s := F)
    have h0 : 0 ≤ ∑ i ∈ F, ‖r k i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith [hCle k]
  have hbound : ∑' q : {x // x ∉ F}, b q ≤ ε / 2 := by
    rw [hbt]
    have e1 : (∑' q : {x // x ∉ F}, ‖v q‖ ^ 2) / (2 * δ) ≤ δ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have e2 : δ * (∑' q : {x // x ∉ F}, ‖r k q‖ ^ 2) / 2 ≤ δ * C' / 2 := by
      have := mul_le_mul_of_nonneg_left hrle hδpos.le
      linarith
    have e3 : δ / 2 + δ * C' / 2 = ε / 2 := by
      rw [hδ]
      field_simp
    linarith
  rw [Real.dist_eq, sub_zero, ← hsplit]
  calc |∑ i ∈ F, f i + ∑' q : {x // x ∉ F}, f q| ≤ |∑ i ∈ F, f i| + |∑' q : {x // x ∉ F}, f q| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1 (htail.trans hbound)
    _ = ε := by ring

/-- **The profile decomposition in the energy space.** -/
theorem exists_profile_decomposition [Countable ι] (g : ι → ℝ) {u : ℕ → ι → ℂ} {C : ℝ}
    (hs : ∀ k, Summable fun i => ‖u k i‖ ^ 2) (hC : ∀ k, energy (u k) ≤ C) (t : ℕ → ℝ) :
    ∃ (v χ : ι → ℂ) (ψ : ℕ → ℕ), StrictMono ψ ∧ (Summable fun i => ‖v i‖ ^ 2) ∧ energy v ≤ C ∧
      (∀ i, ‖χ i‖ = 1) ∧
      (∀ i, Tendsto (fun k => u (ψ k) i) atTop (𝓝 (v i))) ∧
      (∀ i, Tendsto (fun k => cexp (((g i * t (ψ k) : ℝ) : ℂ) * I) * u (ψ k) i) atTop (𝓝 (χ i * v i))) ∧
      Tendsto (fun k => energy (u (ψ k)) - energy (fun i => u (ψ k) i - v i) - energy v) atTop (𝓝 0) ∧
      ∀ F : Finset ι, Tendsto (fun k => ∑ i ∈ F, ‖u (ψ k) i - v i‖ ^ 2) atTop (𝓝 0) := by
  classical
  have hC0 : 0 ≤ C := (energy_nonneg _).trans (hC 0)
  have hbd : ∀ k i, ‖u k i‖ ≤ Real.sqrt C := fun k i => by
    have h1 : ‖u k i‖ ^ 2 ≤ energy (u k) := (hs k).le_tsum i fun j _ => sq_nonneg _
    exact Real.le_sqrt_of_sq_le (h1.trans (hC k))
  have hcpt : IsCompact (Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) (Real.sqrt C)) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨v, -, φ₁, hφ₁, hv⟩ := hcpt.tendsto_subseq (x := u) fun k i _ => by
    simpa using hbd k i
  obtain ⟨χ', φ₂, hφ₂, hχ'⟩ := exists_bohr_subseq (J := Unit) g (fun _ k => t (φ₁ k))
  set ψ := φ₁ ∘ φ₂ with hψ
  have hψm : StrictMono ψ := hφ₁.comp hφ₂
  have hvi : ∀ i, Tendsto (fun k => u (ψ k) i) atTop (𝓝 (v i)) := fun i =>
    ((tendsto_pi_nhds.mp hv) i).comp hφ₂.tendsto_atTop
  -- Fatou
  have hF : ∀ F : Finset ι, ∑ i ∈ F, ‖v i‖ ^ 2 ≤ C := fun F => by
    have hl : Tendsto (fun k => ∑ i ∈ F, ‖u (ψ k) i‖ ^ 2) atTop (𝓝 (∑ i ∈ F, ‖v i‖ ^ 2)) :=
      tendsto_finset_sum _ fun i _ => (hvi i).norm.pow 2
    exact le_of_tendsto' hl fun k =>
      ((hs (ψ k)).sum_le_tsum F fun _ _ => sq_nonneg _).trans (hC (ψ k))
  have hvs : Summable fun i => ‖v i‖ ^ 2 := summable_of_sum_le (fun _ => sq_nonneg _) hF
  have hvC : energy v ≤ C := hasSum_le_of_sum_le hvs.hasSum hF
  have hrs : ∀ k, Summable fun i => ‖u (ψ k) i - v i‖ ^ 2 := fun k => norm_sub_sq_summable (hs _) hvs
  have hrC : ∀ k, energy (fun i => u (ψ k) i - v i) ≤ 2 * C + 2 * C := fun k => by
    have h := Summable.tsum_le_tsum (f := fun i => ‖u (ψ k) i - v i‖ ^ 2)
      (g := fun i => 2 * ‖u (ψ k) i‖ ^ 2 + 2 * ‖v i‖ ^ 2) (fun i => by
        have h0 := norm_sub_le (u (ψ k) i) (v i)
        have h2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
        nlinarith [sq_nonneg (‖u (ψ k) i‖ - ‖v i‖)]) (hrs k) (((hs _).mul_left 2).add (hvs.mul_left 2))
    rw [((hs _).mul_left 2).tsum_add (hvs.mul_left 2), tsum_mul_left, tsum_mul_left] at h
    have h1 := hC (ψ k)
    simp only [energy] at h1 hvC ⊢
    linarith
  have hnull : ∀ i, Tendsto (fun k => u (ψ k) i - v i) atTop (𝓝 0) := fun i => by
    simpa using (hvi i).sub_const (v i)
  have hW := tendsto_tsum_re_zero hvs hrs hrC hnull
  refine ⟨v, fun i => ((χ' () i : Circle) : ℂ), ψ, hψm, hvs, hvC, fun i => by simp, hvi, fun i => ?_, ?_, fun F => ?_⟩
  · exact (tendsto_coe_exp (hχ' () i)).mul (hvi i)
  · have hid : ∀ k, energy (u (ψ k)) - energy (fun i => u (ψ k) i - v i) - energy v =
        2 * ∑' i, (conj (v i) * (u (ψ k) i - v i)).re := fun k => by
      have hsf : Summable fun i => (conj (v i) * (u (ψ k) i - v i)).re := by
        refine Summable.of_norm_bounded ((hvs.add (hrs k)).mul_left (1 / 2)) fun i => ?_
        rw [Real.norm_eq_abs]
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, RCLike.norm_conj]
        nlinarith [sq_nonneg (‖v i‖ - ‖u (ψ k) i - v i‖)]
      have e : energy (u (ψ k)) = energy (fun i => u (ψ k) i - v i) + energy v +
          2 * ∑' i, (conj (v i) * (u (ψ k) i - v i)).re := by
        simp only [energy]
        rw [← tsum_mul_left, ← (hrs k).tsum_add hvs, ← ((hrs k).add hvs).tsum_add (hsf.mul_left 2)]
        refine tsum_congr fun i => ?_
        have e1 : u (ψ k) i = v i + (u (ψ k) i - v i) := by ring
        conv_lhs => rw [e1, norm_add_sq']
        ring
      linarith
    simp only [hid]
    simpa using hW.const_mul 2
  · have h1 : Tendsto (fun k => ∑ i ∈ F, ‖u (ψ k) i - v i‖ ^ 2) atTop (𝓝 (∑ i ∈ F, ‖(0 : ℂ)‖ ^ 2)) :=
      tendsto_finset_sum _ fun i _ => (hnull i).norm.pow 2
    simpa using h1

/-! ### On-line configurations -/

/-- The spectral vector of a test on an on-line configuration. -/
def spectralVector (Z : ZeroConfig) (f : ℝ → ℝ) (ρ : Z.carrier) : ℂ :=
  (Real.sqrt (Z.mult ρ) : ℂ) * paperFT (cx f) (((ρ : ℂ).im : ℝ) : ℂ)

theorem norm_spectralVector_sq (Z : ZeroConfig) (f : ℝ → ℝ) (ρ : Z.carrier) :
    ‖spectralVector Z f ρ‖ ^ 2 = (Z.mult ρ : ℝ) * ‖paperFT (cx f) (((ρ : ℂ).im : ℝ) : ℂ)‖ ^ 2 := by
  rw [spectralVector, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg _)]

/-- On the line the zero summand is the energy density. -/
theorem Wsummand_of_onLine (Z : ZeroConfig) (f : ℝ → ℝ) {ρ : Z.carrier} (hρ : (ρ : ℂ).re = 1 / 2) :
    Z.Wsummand (cx f) (cx f) ρ = ((‖spectralVector Z f ρ‖ ^ 2 : ℝ) : ℂ) := by
  rw [norm_spectralVector_sq, ZeroConfig.Wsummand, gammaOf_of_re_eq_half hρ, Complex.conj_ofReal, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **The Weil energy on the line is the energy of the spectral vector.** -/
theorem re_W_eq_energy {Z : ZeroConfig} (hZ : TemperedConfig Z) (hline : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2)
    {f : ℝ → ℝ} (hf : f ∈ realTests) :
    Summable (fun ρ => ‖spectralVector Z f ρ‖ ^ 2) ∧
      (Z.W (cx f) (cx f)).re = energy (spectralVector Z f) := by
  have hs := summable_Wsummand Z hZ (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
    (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
  have hsr : Summable fun ρ : Z.carrier => ‖spectralVector Z f ρ‖ ^ 2 := by
    refine (hs.mapL Complex.reCLM).congr fun ρ => ?_
    simp [Wsummand_of_onLine Z f (hline ρ ρ.2)]
  refine ⟨hsr, ?_⟩
  rw [ZeroConfig.W, Complex.re_tsum hs, energy]
  refine tsum_congr fun ρ => ?_
  rw [Wsummand_of_onLine Z f (hline ρ ρ.2), Complex.ofReal_re]

/-- A bubble family: `Σ_j c_j f_j(· − t_j)`. -/
def bubbleTest {n : ℕ} (c : Fin n → ℝ) (f : Fin n → ℝ → ℝ) (t : Fin n → ℝ) : ℝ → ℝ :=
  ∑ j, c j • scaleShift (t j) (f j)

theorem bubbleTest_mem {n : ℕ} (c : Fin n → ℝ) {f : Fin n → ℝ → ℝ} (hf : ∀ j, f j ∈ realTests)
    (t : Fin n → ℝ) : bubbleTest c f t ∈ realTests :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (scaleShift_mem (t j) (hf j))

/-- The transform of a bubble family is the sum of the characters times the transforms. -/
theorem paperFT_bubbleTest {n : ℕ} (c : Fin n → ℝ) {f : Fin n → ℝ → ℝ} (hf : ∀ j, f j ∈ realTests)
    (t : Fin n → ℝ) (z : ℂ) :
    paperFT (cx (bubbleTest c f t)) z =
      ∑ j, (c j : ℂ) * cexp (t j * (I * z)) * paperFT (cx (f j)) z := by
  classical
  have hgen : ∀ S : Finset (Fin n), paperFT (cx (∑ j ∈ S, c j • scaleShift (t j) (f j))) z =
      ∑ j ∈ S, (c j : ℂ) * cexp (t j * (I * z)) * paperFT (cx (f j)) z := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [cx, paperFT]
    | insert a S ha ih =>
      have hmem : (∑ j ∈ S, c j • scaleShift (t j) (f j)) ∈ realTests :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (scaleShift_mem (t j) (hf j))
      have ha' : (c a • scaleShift (t a) (f a)) ∈ realTests :=
        Submodule.smul_mem _ _ (scaleShift_mem (t a) (hf a))
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, ← mul_comm (cexp _), ]
      have hcx : cx (c a • scaleShift (t a) (f a) + ∑ j ∈ S, c j • scaleShift (t j) (f j)) =
          fun u => cx (c a • scaleShift (t a) (f a)) u + (1 : ℂ) * cx (∑ j ∈ S, c j • scaleShift (t j) (f j)) u := by
        funext u
        simp [cx]
      have hc1 := (cx_contDiff ha'.1).continuous
      have hc2 := (cx_contDiff hmem.1).continuous
      rw [hcx, ZeroConfigurationGeometry.paperFT_add_smul hc1 (cx_hasCompactSupport ha'.2) hc2
        (cx_hasCompactSupport hmem.2), one_mul]
      have hsm : cx (c a • scaleShift (t a) (f a)) =
          fun u => 0 + (c a : ℂ) * cx (scaleShift (t a) (f a)) u := by
        funext u
        simp [cx]
      congr 1
      have hz0 : paperFT (cx (c a • scaleShift (t a) (f a))) z =
          (c a : ℂ) * paperFT (cx (scaleShift (t a) (f a))) z := by
        have hc3 := (cx_contDiff (scaleShift_mem (t a) (hf a)).1).continuous
        have hfz := ZeroConfigurationGeometry.paperFT_add_smul (f := fun _ => (0 : ℂ))
          (g := cx (scaleShift (t a) (f a))) continuous_const HasCompactSupport.zero hc3
          (cx_hasCompactSupport (scaleShift_mem (t a) (hf a)).2) (c a : ℂ) z
        have e0 : paperFT (fun _ => (0 : ℂ)) z = 0 := by simp [paperFT]
        rw [e0, zero_add] at hfz
        rw [hsm, hfz]
      rw [hz0, paperFT_cx_scaleShift_apply]
      ring
  exact hgen Finset.univ

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
