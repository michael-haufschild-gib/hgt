import GaloisForLFunctions.WindowVisibilityLaw.ShallowClusterExclusionAndTaperedCrystalBarrier
import GaloisForLFunctions.WindowVisibilityLaw.TheSamplingInequalityAtAFreeWindow

/-!
# The universal visibility threshold

The exact law `k · pairEnergy(δ, a) ≤ L` was known for one configuration, the doubled lattice with a
site of multiplicity `k`. Here is its necessity half for every configuration: if the sea around an
off-line site of multiplicity `k` has depth at most `σ` and at most `K` zeros in each cell of length
`2π/ℓ`, then window positivity at `a` forces

`k · pairEnergy(δ, a) ≤ (K/2) ℓ e^{2(2π/ℓ + σ)a}`.

At `K = 2`, `ℓ = L`, `σ = 0` the right side is `L (1 + O(a/L))`: the sharp constant `e^{2δa} ≲ 4δL/k`
holds for every configuration as regular as a lattice at the scale of its spacing, not only for
lattices.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold
open _root_.RHTower.CCMParityQuartet

/-- Cell sampling on a finite part of a zero configuration, counted with multiplicity. -/
theorem sum_mult_norm_sq_paperFT_le_of_cellCount (Z : ZeroConfig) {b ℓ σ : ℝ} (hb : 0 < b)
    (hℓ : 2 * b < ℓ) (hσ : 0 ≤ σ) {f : ℝ → ℂ} (hf : IntervalSource b f) (F : Finset ℂ)
    (hFσ : ∀ ρ ∈ F, |ρ.re - 1 / 2| ≤ σ) {K : ℕ}
    (hcell : ∀ n : ℤ, ∑ ρ ∈ F.filter (fun ρ => ⌊ρ.im / (2 * π / ℓ)⌋ = n), Z.mult ρ ≤ K) :
    (∑ ρ ∈ F, (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 ≤
        Real.exp (2 * (2 * π / ℓ + σ) * b) * (K * (ℓ * ∫ u, ‖f u‖ ^ 2))) ∧
      ∑ ρ ∈ F, (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2 ≤
        Real.exp (2 * (2 * π / ℓ + σ) * b) * (K * (ℓ * ∫ u, ‖f u‖ ^ 2)) := by
  classical
  let ι := Σ ρ : F, Fin (Z.mult ρ)
  let x : ι → ℝ := fun q => (q.1 : ℂ).im
  have hK : ∀ n : ℤ, ((Finset.univ : Finset ι).filter
      fun q => ⌊x q / (2 * π / ℓ)⌋ = n).card ≤ K := by
    intro n
    have hcard_eq : ((Finset.univ : Finset ι).filter fun q => ⌊x q / (2 * π / ℓ)⌋ = n).card =
        ∑ ρ ∈ F.filter (fun ρ => ⌊ρ.im / (2 * π / ℓ)⌋ = n), Z.mult ρ := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sigma, Finset.sum_filter]
      refine (Finset.sum_congr rfl fun ρ _ => ?_).trans
        (Finset.univ_eq_attach (s := F) ▸ Finset.sum_attach F
          fun ρ => if ⌊ρ.im / (2 * π / ℓ)⌋ = n then Z.mult ρ else 0)
      by_cases h : ⌊(ρ : ℂ).im / (2 * π / ℓ)⌋ = n <;> simp [x, h]
    rw [hcard_eq]
    exact hcell n
  let y₁ : ι → ℝ := fun q => 1 / 2 - (q.1 : ℂ).re
  let y₂ : ι → ℝ := fun q => (q.1 : ℂ).re - 1 / 2
  have hy₁ : ∀ q, |y₁ q| ≤ σ := fun q => by
    dsimp [y₁]; rw [abs_sub_comm]; exact hFσ q.1 q.1.2
  have hy₂ : ∀ q, |y₂ q| ≤ σ := fun q => hFσ q.1 q.1.2
  have hs₁ := sum_norm_sq_testTransform_le_of_cellCount hb hℓ hf x y₁ hσ hy₁ Finset.univ hK
  have hs₂ := sum_norm_sq_testTransform_le_of_cellCount hb hℓ hf x y₂ hσ hy₂ Finset.univ hK
  have hft_eq : ∀ z, paperFT f z = testTransform f z := fun _ => rfl
  have hsum₁ : (∑ q : ι, ‖testTransform f ((x q : ℂ) + (y₁ q : ℂ) * I)‖ ^ 2) =
      ∑ ρ ∈ F, (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 := by
    rw [Fintype.sum_sigma]
    refine (Finset.sum_congr rfl fun ρ _ => ?_).trans
      (Finset.univ_eq_attach (s := F) ▸ Finset.sum_attach F
        fun ρ => (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2)
    have hg : ((ρ : ℂ).im : ℂ) + ((1 / 2 - (ρ : ℂ).re : ℝ) : ℂ) * I = gammaOf ρ := by
      apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im]
    dsimp only [x, y₁]
    rw [hg, ← hft_eq]
    simp
  have hsum₂ : (∑ q : ι, ‖testTransform f ((x q : ℂ) + (y₂ q : ℂ) * I)‖ ^ 2) =
      ∑ ρ ∈ F, (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2 := by
    rw [Fintype.sum_sigma]
    refine (Finset.sum_congr rfl fun ρ _ => ?_).trans
      (Finset.univ_eq_attach (s := F) ▸ Finset.sum_attach F
        fun ρ => (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2)
    have hg : ((ρ : ℂ).im : ℂ) + (((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ) * I = conj (gammaOf ρ) := by
      apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im]
    dsimp only [x, y₂]
    rw [hg, ← hft_eq]
    simp
  exact ⟨hsum₁ ▸ hs₁, hsum₂ ▸ hs₂⟩

/-- The truncated optimal tilt: `sinh(δu)` cut off between `a'` and `a`, modulated to `γ₀`. -/
theorem exists_truncated_tilt_test {δ a a' : ℝ} (hδ : 0 < δ) (γ₀ : ℝ) (ha' : 0 < a') (ha'a : a' < a) :
    ∃ (f : ℝ → ℂ) (Is : ℝ), ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      (∫ u, ‖f u‖ ^ 2) ≤ pairEnergy δ a ∧ pairEnergy δ a' ≤ Is ∧
      paperFT f ((γ₀ : ℂ) - I * δ) = (Is : ℂ) ∧ paperFT f ((γ₀ : ℂ) + I * δ) = -(Is : ℂ) := by
  have ha : 0 < a := ha'.trans ha'a
  set φ : ContDiffBump (0 : ℝ) := ⟨a', a, ha', ha'a⟩
  set s : ℝ → ℝ := fun u => Real.sinh (δ * u) * φ u
  set f : ℝ → ℂ := fun u => (s u : ℂ) * cexp (-(I * γ₀ * u))
  have hsc : ContDiff ℝ 2 s :=
    (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).mul φ.contDiff
  have hexpc : ContDiff ℝ 2 (fun u : ℝ => cexp (-(I * γ₀ * u))) :=
    Complex.contDiff_exp.comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg)
  have hfc2 : ContDiff ℝ 2 f := (Complex.ofRealCLM.contDiff.comp hsc).mul hexpc
  have hsupp_s : ∀ u, u ∉ Icc (-a) a → s u = 0 := fun u hu => by
    have hφ0 : φ u = 0 := φ.zero_of_le_dist (by
      rw [Real.dist_eq, sub_zero]
      by_contra hlt
      rw [not_le] at hlt
      exact hu ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩)
    simp [s, hφ0]
  have hfs : tsupport f ⊆ Icc (-a) a := closure_minimal (fun u hu => by
    by_contra hnot
    exact hu (by simp [f, hsupp_s u hnot])) isClosed_Icc
  have hscs : HasCompactSupport s :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => hsupp_s u hu
  have hA : paperFT f ((γ₀ : ℂ) - I * δ) = ((∫ u, s u * Real.exp (δ * u) : ℝ) : ℂ) := by
    rw [paperFT_sub_I_mul, paperFT_def, ← integral_complex_ofReal]
    congr 1 with u
    simp only [f]
    have hc : cexp (-(I * γ₀ * u)) * cexp (I * γ₀ * u) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [Complex.ofReal_mul (s u) (Real.exp (δ * u))]
    linear_combination (s u : ℂ) * (Real.exp (δ * u) : ℂ) * hc
  have hB : paperFT f ((γ₀ : ℂ) + I * δ) = ((∫ u, s u * Real.exp (-δ * u) : ℝ) : ℂ) := by
    rw [paperFT_add_I_mul, paperFT_def, ← integral_complex_ofReal]
    congr 1 with u
    simp only [f]
    have hc : cexp (-(I * γ₀ * u)) * cexp (I * γ₀ * u) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [Complex.ofReal_mul (s u) (Real.exp (-δ * u))]
    linear_combination (s u : ℂ) * (Real.exp (-δ * u) : ℂ) * hc
  set Ap := ∫ u, s u * Real.exp (δ * u)
  set Bp := ∫ u, s u * Real.exp (-δ * u)
  set Is := ∫ u, φ u * Real.sinh (δ * u) ^ 2
  have hint : ∀ c : ℝ, Integrable (fun u => s u * Real.exp (c * u)) := fun c =>
    (hsc.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hscs.mul_right
  have hodd : ∫ u, s u * Real.cosh (δ * u) = 0 :=
    RHTower.integral_odd_mul_cosh (fun u => by
      simp only [s, φ.neg, mul_neg, Real.sinh_neg, neg_mul]) δ
  have hsum : Ap + Bp = 0 := by
    dsimp only [Ap, Bp]
    rw [← integral_add (hint δ) (hint (-δ))]
    have h2 : ∫ u, (s u * Real.exp (δ * u) + s u * Real.exp (-δ * u)) =
        2 * ∫ u, s u * Real.cosh (δ * u) := by
      rw [← integral_const_mul]
      congr 1 with u
      rw [Real.cosh_eq, show -δ * u = -(δ * u) by ring]
      ring
    rw [h2, hodd, mul_zero]
  have hsub : Ap - Bp = 2 * Is := by
    dsimp only [Ap, Bp, Is]
    rw [← integral_sub (hint δ) (hint (-δ)), ← integral_const_mul]
    congr 1 with u
    simp only [s]
    rw [Real.sinh_eq (δ * u), show -δ * u = -(δ * u) by ring]
    ring
  have hApv : Ap = Is := by linarith
  have hBpv : Bp = -Is := by linarith
  have hnormf : ∀ u, ‖f u‖ ^ 2 = s u ^ 2 := fun u => by
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he : ‖cexp (-(I * (γ₀ : ℂ) * (u : ℂ)))‖ = 1 := by
      rw [show -(I * (γ₀ : ℂ) * (u : ℂ)) = I * ((-γ₀ : ℝ) : ℂ) * u by push_cast; ring,
        norm_cexp_I_mul]
      simp
    rw [he, mul_one, sq_abs]
  have hupper : ∫ u, ‖f u‖ ^ 2 ≤ pairEnergy δ a := by
    simp_rw [hnormf]
    rw [← integral_sinh_sq_Icc hδ ha.le, ← integral_indicator measurableSet_Icc]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
      (((by fun_prop : Continuous fun u : ℝ => Real.sinh (δ * u) ^ 2).integrableOn_Icc
        ).integrable_indicator measurableSet_Icc) (Eventually.of_forall fun u => ?_)
    dsimp only
    by_cases hu : u ∈ Icc (-a) a
    · rw [Set.indicator_of_mem hu]
      simp only [s, mul_pow]
      have h1 : φ u ^ 2 ≤ 1 := by
        have := φ.le_one (x := u); have := φ.nonneg (x := u); nlinarith
      nlinarith [sq_nonneg (Real.sinh (δ * u))]
    · rw [Set.indicator_of_notMem hu, hsupp_s u hu]
      norm_num
  have hlower : pairEnergy δ a' ≤ Is := by
    rw [← integral_sinh_sq_Icc hδ ha'.le, ← integral_indicator measurableSet_Icc]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun u => Set.indicator_nonneg (fun _ _ => sq_nonneg _) u)
      ((φ.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        (φ.hasCompactSupport.mul_right)) (Eventually.of_forall fun u => ?_)
    dsimp only
    by_cases hu : u ∈ Icc (-a') a'
    · rw [Set.indicator_of_mem hu, φ.one_of_mem_closedBall]
      · ring_nf; exact le_rfl
      · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
        exact ⟨hu.1, hu.2⟩
    · rw [Set.indicator_of_notMem hu]
      exact mul_nonneg φ.nonneg (sq_nonneg _)
  refine ⟨f, Is, hfc2, hfs, hupper, hlower, ?_, ?_⟩
  · rw [hA, hApv]
  · rw [hB, hBpv]
    push_cast
    rfl

/-- **The universal visibility threshold.** If the sea around an off-line site of multiplicity `k`
and depth `δ` has depth at most `σ` and at most `K` zeros per cell of length `2π/ℓ`, `ℓ > 2a`, then
window positivity at `a` forces `k · pairEnergy(δ, a) ≤ (K/2) ℓ e^{2(2π/ℓ + σ)a}`. -/
theorem pairEnergy_le_of_windowPositiveAt_of_cellCount {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {a ℓ δ σ γ₀ : ℝ} {K : ℕ} (ha : 0 < a) (hℓ : 2 * a < ℓ) (hδ : 0 < δ) (hσ : 0 ≤ σ) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hre : ρ₀.re = 1 / 2 + δ) (him : ρ₀.im = γ₀)
    (hsea : ∀ ρ ∈ Z.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.re - 1 / 2| ≤ σ)
    (hcell : ∀ F : Finset ℂ, (∀ ρ ∈ F, ρ ∈ Z.carrier ∧ ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀) → ∀ n : ℤ,
      ∑ ρ ∈ F.filter (fun ρ => ⌊ρ.im / (2 * π / ℓ)⌋ = n), Z.mult ρ ≤ K)
    (hpos : WindowPositiveAt Z a) :
    (Z.mult ρ₀ : ℝ) * pairEnergy δ a ≤
      (K / 2 : ℝ) * ℓ * Real.exp (2 * (2 * π / ℓ + σ) * a) := by
  classical
  obtain ⟨E, hEd⟩ : ∃ E, E = (K / 2 : ℝ) * ℓ * Real.exp (2 * (2 * π / ℓ + σ) * a) := ⟨_, rfl⟩
  rw [← hEd]
  have hℓ0 : 0 < ℓ := by linarith only [ha, hℓ]
  have hE0 : 0 ≤ E := by rw [hEd]; positivity
  have hk1 : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  by_contra hlt
  rw [not_le] at hlt
  have hSa0 : 0 < pairEnergy δ a := by
    by_contra hn
    rw [not_lt] at hn
    have := mul_le_mul_of_nonneg_left hn (by linarith only [hk1] : (0 : ℝ) ≤ Z.mult ρ₀)
    linarith only [this, hE0, hlt]
  have hmain : E * pairEnergy δ a < (Z.mult ρ₀ : ℝ) * pairEnergy δ a ^ 2 := by
    have := mul_lt_mul_of_pos_right hlt hSa0
    calc E * pairEnergy δ a < (Z.mult ρ₀ : ℝ) * pairEnergy δ a * pairEnergy δ a := this
      _ = _ := by ring
  have hcont : Continuous fun x : ℝ => (Z.mult ρ₀ : ℝ) * pairEnergy δ x ^ 2 :=
    continuous_const.mul ((continuous_pairEnergy δ).pow 2)
  have hev : ∀ᶠ x in 𝓝[<] a, E * pairEnergy δ a < (Z.mult ρ₀ : ℝ) * pairEnergy δ x ^ 2 ∧ a / 2 < x :=
    ((hcont.continuousAt.eventually (lt_mem_nhds hmain)).and
      (continuous_id.continuousAt.eventually (lt_mem_nhds (by linarith : a / 2 < a)))).filter_mono
      nhdsWithin_le_nhds
  obtain ⟨a', ⟨hSa', ha'2⟩, ha'a⟩ := (hev.and self_mem_nhdsWithin).exists
  have ha'0 : 0 < a' := by linarith only [ha, ha'2]
  obtain ⟨f, Is, hf, hfs, hNf, hIs, hF1, hF2⟩ := exists_truncated_tilt_test hδ γ₀ ha'0 ha'a
  have hIs0 : 0 ≤ Is := (pairEnergy_nonneg hδ ha'0.le).trans hIs
  have hNf0 : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hfsrc : IntervalSource a f :=
    { continuous := hf.continuous
      hasCompactSupport := hasCompactSupport_of_tsupport_subset_Icc hfs
      vanish := fun u hu => image_eq_zero_of_notMem_tsupport fun hm => hu (hfs hm) }
  have hsumm := summable_Wsummand_of_tempered hZ ha.le hf hfs
  have hρr : reflect ρ₀ ∈ Z.carrier := Z.reflect_mem ρ₀ hρ₀
  have hne : (⟨ρ₀, hρ₀⟩ : Z.carrier) ≠ ⟨reflect ρ₀, hρr⟩ := by
    intro h
    have h1 : ρ₀ = reflect ρ₀ := congrArg Subtype.val h
    have h2 := congrArg Complex.re h1
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at h2
    linarith only [h2, hre, hδ]
  let P : Finset Z.carrier := {⟨ρ₀, hρ₀⟩, ⟨reflect ρ₀, hρr⟩}
  have hsplit := hsumm.sum_add_tsum_compl (s := P)
  have hP : ∑ τ ∈ P, Z.Wsummand f f τ =
      Z.Wsummand f f ρ₀ + Z.Wsummand f f (reflect ρ₀) := Finset.sum_pair hne
  have hγ : gammaOf ρ₀ = (γ₀ : ℂ) - I * δ := by
    apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im, hre, him]
  have hγc : conj (gammaOf ρ₀) = (γ₀ : ℂ) + I * δ := by
    rw [hγ]
    apply Complex.ext <;> simp
  have hW0 : Z.Wsummand f f ρ₀ = -(((Z.mult ρ₀ : ℝ) * Is ^ 2 : ℝ) : ℂ) := by
    rw [ZeroConfig.Wsummand, hγc, hγ, hF1, hF2, map_neg, Complex.conj_ofReal]
    push_cast
    ring
  have hW1 : Z.Wsummand f f (reflect ρ₀) = -(((Z.mult ρ₀ : ℝ) * Is ^ 2 : ℝ) : ℂ) := by
    rw [ZeroConfig.Wsummand, gammaOf_reflect_eq_conj, Complex.conj_conj, hγc, hγ, hF1, hF2,
      Complex.conj_ofReal, Z.mult_reflect ρ₀ hρ₀]
    push_cast
    ring
  -- The sea.
  obtain ⟨B, hBd⟩ : ∃ B, B = Real.exp (2 * (2 * π / ℓ + σ) * a) * (K * (ℓ * ∫ u, ‖f u‖ ^ 2)) :=
    ⟨_, rfl⟩
  have hfinite : ∀ t : Finset (↑((P : Set Z.carrier)ᶜ)),
      ∑ τ ∈ t, ‖Z.Wsummand f f ((τ : Z.carrier) : ℂ)‖ ≤ B := by
    intro t
    let e : ↑((P : Set Z.carrier)ᶜ) → ℂ := fun τ => ((τ : Z.carrier) : ℂ)
    have hinj : Function.Injective e := fun u v h => Subtype.ext (Subtype.ext h)
    let F : Finset ℂ := t.image e
    have hsumF : ∑ τ ∈ t, ‖Z.Wsummand f f ((τ : Z.carrier) : ℂ)‖ =
        ∑ ρ ∈ F, ‖Z.Wsummand f f ρ‖ := by
      rw [Finset.sum_image fun u _ v _ h => hinj h]
    have hFprop : ∀ ρ ∈ F, ρ ∈ Z.carrier ∧ ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ := by
      intro ρ hρ
      obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hρ
      have hτ := τ.2
      refine ⟨(τ : Z.carrier).2, fun h => hτ ?_, fun h => hτ ?_⟩
      · have : (τ : Z.carrier) = ⟨ρ₀, hρ₀⟩ := Subtype.ext h
        simp [P, this]
      · have : (τ : Z.carrier) = ⟨reflect ρ₀, hρr⟩ := Subtype.ext h
        simp [P, this]
    have hFσ : ∀ ρ ∈ F, |ρ.re - 1 / 2| ≤ σ := fun ρ hρ =>
      hsea ρ (hFprop ρ hρ).1 (hFprop ρ hρ).2.1 (hFprop ρ hρ).2.2
    obtain ⟨h1, h2⟩ := sum_mult_norm_sq_paperFT_le_of_cellCount Z ha hℓ hσ hfsrc F hFσ
      (hcell F hFprop)
    rw [← hBd] at h1 h2
    rw [hsumF]
    have hpt : ∀ ρ ∈ F, ‖Z.Wsummand f f ρ‖ ≤ (1 / 2) * ((Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 +
        (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) := fun ρ _ => by
      rw [ZeroConfig.Wsummand, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]
      have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
      nlinarith only [mul_nonneg hm0 (sq_nonneg (‖paperFT f (gammaOf ρ)‖ -
        ‖paperFT f (conj (gammaOf ρ))‖))]
    calc ∑ ρ ∈ F, ‖Z.Wsummand f f ρ‖
        ≤ ∑ ρ ∈ F, (1 / 2) * ((Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 +
          (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) := Finset.sum_le_sum hpt
      _ = (1 / 2) * ((∑ ρ ∈ F, (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2) +
          ∑ ρ ∈ F, (Z.mult ρ : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ B := by linarith only [h1, h2]
  have hsn : Summable fun τ : ↑((P : Set Z.carrier)ᶜ) =>
      ‖Z.Wsummand f f ((τ : Z.carrier) : ℂ)‖ :=
    (hsumm.norm).subtype _
  have hrest : ‖∑' τ : ↑((P : Set Z.carrier)ᶜ), Z.Wsummand f f ((τ : Z.carrier) : ℂ)‖ ≤ B :=
    (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_of_sum_le hfinite)
  have hWre : (Z.W f f).re ≤ -(2 * ((Z.mult ρ₀ : ℝ) * Is ^ 2)) + B := by
    have hW : Z.W f f = -(((Z.mult ρ₀ : ℝ) * Is ^ 2 : ℝ) : ℂ) + -(((Z.mult ρ₀ : ℝ) * Is ^ 2 : ℝ) : ℂ) +
        ∑' τ : ↑((P : Set Z.carrier)ᶜ), Z.Wsummand f f ((τ : Z.carrier) : ℂ) := by
      rw [ZeroConfig.W, ← hsplit, hP, hW0, hW1]
    rw [hW, Complex.add_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    have := (Complex.re_le_norm _).trans hrest
    linarith only [this]
  have h0 := hpos f hf hfs
  have hB2 : B ≤ 2 * (E * pairEnergy δ a) := by
    rw [hBd, hEd]
    have h1 : Real.exp (2 * (2 * π / ℓ + σ) * a) * (K * (ℓ * ∫ u, ‖f u‖ ^ 2)) =
        (Real.exp (2 * (2 * π / ℓ + σ) * a) * (K * ℓ)) * ∫ u, ‖f u‖ ^ 2 := by ring
    rw [h1]
    calc _ ≤ (Real.exp (2 * (2 * π / ℓ + σ) * a) * (K * ℓ)) * pairEnergy δ a :=
          mul_le_mul_of_nonneg_left hNf (by positivity)
      _ = _ := by ring
  have hIs2 : pairEnergy δ a' ^ 2 ≤ Is ^ 2 :=
    pow_le_pow_left₀ (pairEnergy_nonneg hδ ha'0.le) hIs 2
  have hk0 : (0 : ℝ) ≤ Z.mult ρ₀ := Nat.cast_nonneg _
  have hkIs := mul_le_mul_of_nonneg_left hIs2 hk0
  linarith only [hWre, h0, hB2, hkIs, hSa']

/-- **The sharp form `e^{2δa} ≲ 4δL/k`.** With `E = (K/2) ℓ e^{2(2π/ℓ+σ)a}`, the threshold reads
`e^{2δa} ≤ 4δ(E/k + a) + 1`. -/
theorem exp_two_mul_le_of_windowPositiveAt_of_cellCount {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {a ℓ δ σ γ₀ : ℝ} {K : ℕ} (ha : 0 < a) (hℓ : 2 * a < ℓ) (hδ : 0 < δ) (hσ : 0 ≤ σ) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hre : ρ₀.re = 1 / 2 + δ) (him : ρ₀.im = γ₀)
    (hsea : ∀ ρ ∈ Z.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.re - 1 / 2| ≤ σ)
    (hcell : ∀ F : Finset ℂ, (∀ ρ ∈ F, ρ ∈ Z.carrier ∧ ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀) → ∀ n : ℤ,
      ∑ ρ ∈ F.filter (fun ρ => ⌊ρ.im / (2 * π / ℓ)⌋ = n), Z.mult ρ ≤ K)
    (hpos : WindowPositiveAt Z a) :
    Real.exp (2 * δ * a) ≤
      4 * δ * ((K / 2 : ℝ) * ℓ * Real.exp (2 * (2 * π / ℓ + σ) * a) / (Z.mult ρ₀ : ℝ) + a) + 1 := by
  have h := pairEnergy_le_of_windowPositiveAt_of_cellCount hZ ha hℓ hδ hσ hρ₀ hre him hsea hcell hpos
  obtain ⟨E, hEd⟩ : ∃ E, E = (K / 2 : ℝ) * ℓ * Real.exp (2 * (2 * π / ℓ + σ) * a) := ⟨_, rfl⟩
  rw [← hEd] at h ⊢
  have hk0 : (0 : ℝ) < Z.mult ρ₀ := by
    have h1 : 0 < Z.mult ρ₀ := Z.one_le_mult ρ₀ hρ₀
    exact_mod_cast h1
  have hS : pairEnergy δ a ≤ E / (Z.mult ρ₀ : ℝ) := by
    rw [le_div_iff₀ hk0]
    linarith only [h]
  unfold pairEnergy at hS
  have hsinh : Real.sinh (2 * δ * a) ≤ 2 * δ * (E / (Z.mult ρ₀ : ℝ) + a) := by
    have h1 : Real.sinh (2 * δ * a) / (2 * δ) ≤ E / (Z.mult ρ₀ : ℝ) + a := by linarith only [hS]
    calc Real.sinh (2 * δ * a) ≤ (E / (Z.mult ρ₀ : ℝ) + a) * (2 * δ) :=
          (div_le_iff₀ (by positivity)).mp h1
      _ = _ := by ring
  have hsmall : Real.exp (-(2 * δ * a)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 2 * δ * a := by positivity
    linarith only [this]
  rw [Real.sinh_eq] at hsinh
  linarith only [hsinh, hsmall]

end GaloisForLFunctions.WindowVisibilityLaw
