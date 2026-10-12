import GaloisForLFunctions.RHTower.XiCosineShiftBoundedCluster
import GaloisForLFunctions.HTGeometry.AveragedRadiusSelection

/-!
# Only dense clusters of deep zeros can mask the cosine producer

Let `ζ₀ = γ₀ + iδ` be the spectral point of a zero copy of `ξ`, and let `h, r, s₀ > 0`.

**Theorem** (`exists_zero_cosShiftXi_of_sparseCluster`). There are `L, c > 0` and `T₀`, depending
only on `h, r, s₀`, with the following property. Suppose `γ₀ ≥ T₀`, `η ≥ 0` and
`η + h + r + s₀ ≤ δ`, and suppose at most `c log γ₀` copies within horizontal distance `L` of `ζ₀`
have `|Im| > η`. Then `cos(hD)Ξ` vanishes within `r` of `ζ₀ − ih`, above height `η`.

A window of length `L` holds `≍ log γ₀` zero copies. So a deep zero can be absorbed by
`cos(hD)` at large height only if a fixed positive proportion of the copies near it have
`|Im| > η`. By Backlund's theorem, the Lindelöf hypothesis is equivalent to
`#{ρ : |β − ½| > η, T < γ ≤ T + 1} = o(log T)` for every `η > 0`. Under it no such cluster exists
(`eventually_im_le_of_cosShiftXi_real_of_sparse`): a real-rooted cosine level `h` then forces
`|β − ½| ≤ h + ε` for all zeros of large height.

**Proof.** As in the bounded-cluster law, with the pigeonhole radius replaced by an averaged one
(`exists_mem_Icc_sum_rpow_le`). On the chosen circle the near deep copies satisfy
`Σ |r' − |ζ − ζ₀||^{−1/2} ≤ #S · 3√2/√r`, and each one costs a factor
`1 + 2h/d ≤ exp(2√(2h/d))`. Their total cost is therefore `exp(O(#S))`, not `exp(O(#S log #S))`.
The Riemann–von Mangoldt crowd gains `κ₀ log γ₀/(2π)`. Far deep copies cost a quarter of that, and
a cluster of at most `c log γ₀` copies costs at most an eighth.
-/

open Complex ComplexConjugate Filter Topology Set Polynomial Metric

namespace RHTower.CosineSparseCluster

open GaloisForLFunctions.HTGeometry RHTower.DeBruijn RHTower.CosineDefectBudget
  RHTower.CrowdedPersistence RHTower.CosineCrowdedPersistence RHTower.CosineIsolatedDeepZero
  RHTower.CosineBoundedCluster

noncomputable section

/-- `log(1 + t) ≤ 2√t` for `t ≥ 0`. -/
theorem one_add_le_exp_two_sqrt {t : ℝ} (ht : 0 ≤ t) : 1 + t ≤ Real.exp (2 * Real.sqrt t) := by
  have h := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt t)
  have hs := Real.sq_sqrt ht
  have h0 := Real.sqrt_nonneg t
  nlinarith

/-- **A separated near copy, exponential form.** -/
theorem norm_shift_le_exp_of_separated {z ζ ζ₀ : ℂ} {h r' : ℝ} (hh : 0 ≤ h)
    (hz : ‖z - (ζ₀ - h * I)‖ = r') (hsep : r' ≠ ‖ζ - ζ₀‖) :
    ‖z - h * I - ζ‖ ≤
        Real.exp (2 * Real.sqrt (2 * h) * |r' - ‖ζ - ζ₀‖| ^ (-(1 / 2) : ℝ)) *
          ‖z + h * I - ζ‖ ∧ 0 < ‖z + h * I - ζ‖ := by
  set ε := |r' - ‖ζ - ζ₀‖| with hε
  have hε0 : 0 < ε := abs_pos.mpr (sub_ne_zero.mpr hsep)
  obtain ⟨h1, h2⟩ := norm_shift_le_of_separated hh hε0 hz le_rfl
  refine ⟨h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)), h2⟩
  have e : 2 * Real.sqrt (2 * h) * ε ^ (-(1 / 2) : ℝ) = 2 * Real.sqrt (2 * h / ε) := by
    rw [Real.sqrt_div' _ hε0.le, Real.rpow_neg hε0.le, ← Real.sqrt_eq_rpow]
    ring
  rw [e]
  exact one_add_le_exp_two_sqrt (by positivity)

/-- **The exceptional product for a sparse cluster.** On the circle of radius `r'`, if `S` contains
every near copy with `|Im| > η` and `r'` avoids all their distances to `ζ₀`, any finite family of
copies with `Im > η` changes the modulus by at most
`exp(2√(2h) Σ_S |r' − |ζ − ζ₀||^{−1/2}) · exp(8h Σ_ρ 1/(L² + (γ₀ − γ)²))`. -/
theorem prod_shift_le_of_sparse {q₀ : XiZeroCopy} {η h r' L : ℝ} (hh : 0 ≤ h) (hr' : 0 ≤ r')
    (hL : 2 * r' ≤ L) (hL1 : 1 ≤ L) (S : Finset XiZeroCopy)
    (hS : ∀ q, |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ L →
      η < |(xiSpectralPoint q).im| → q ∈ S)
    (hsep : ∀ q ∈ S, r' ≠ ‖xiSpectralPoint q - xiSpectralPoint q₀‖)
    (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, η < (xiSpectralPoint q).im) {z : ℂ}
    (hz : ‖z - (xiSpectralPoint q₀ - h * I)‖ = r') (hzim : 0 ≤ z.im) :
    (F.val.map fun q => ‖z - h * I - xiSpectralPoint q‖).prod ≤
        Real.exp (2 * Real.sqrt (2 * h) *
            ∑ q ∈ S, |r' - ‖xiSpectralPoint q - xiSpectralPoint q₀‖| ^ (-(1 / 2) : ℝ)) *
          Real.exp (8 * h * lorentzMassW L (xiSpectralPoint q₀).re) *
          (F.val.map fun q => ‖z + h * I - xiSpectralPoint q‖).prod ∧
      ∀ q ∈ F, z + h * I ≠ xiSpectralPoint q := by
  classical
  set ζ₀ := xiSpectralPoint q₀ with hζ₀_def
  have hL0 : 0 < L := by linarith
  set w : XiZeroCopy → ℝ := fun q => |r' - ‖xiSpectralPoint q - ζ₀‖| ^ (-(1 / 2) : ℝ) with hw
  set near : XiZeroCopy → Prop := fun q => |(xiSpectralPoint q).re - ζ₀.re| ≤ L with hnear
  set f : XiZeroCopy → ℝ := fun q =>
    if near q then Real.exp (2 * Real.sqrt (2 * h) * w q)
    else Real.exp (8 * h * lorentzMassWTerm L ζ₀.re q) with hf
  have hone : ∀ q ∈ F, ‖z - h * I - xiSpectralPoint q‖ ≤ f q * ‖z + h * I - xiSpectralPoint q‖ ∧
      0 < ‖z + h * I - xiSpectralPoint q‖ := by
    intro q hq
    have hdeep : η < |(xiSpectralPoint q).im| := (hF q hq).trans_le (le_abs_self _)
    by_cases hn : near q
    · simp only [hf, hn, if_true]
      exact norm_shift_le_exp_of_separated hh hz (hsep q (hS q hn hdeep))
    · simp only [hf, hn, if_false]
      rw [hnear, not_le] at hn
      rw [lorentzMassWTerm_eq]
      exact norm_shift_le_far hh hr' hz.le hzim
        ((le_abs_self _).trans (abs_xiSpectralPoint_im_le q)) hL hL0 hn.le
  refine ⟨?_, fun q hq h0 => by
    have := (hone q hq).2
    rw [h0, sub_self, norm_zero] at this
    exact lt_irrefl _ this⟩
  rw [← Finset.prod_eq_multiset_prod, ← Finset.prod_eq_multiset_prod]
  have h1 : ∏ q ∈ F, ‖z - h * I - xiSpectralPoint q‖ ≤
      (∏ q ∈ F, f q) * ∏ q ∈ F, ‖z + h * I - xiSpectralPoint q‖ := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q hq => (hone q hq).1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun q _ => norm_nonneg _))
  rw [hf, Finset.prod_ite]
  have hw0 : ∀ q, 0 ≤ w q := fun q => Real.rpow_nonneg (abs_nonneg _) _
  apply mul_le_mul
  · rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun q _ _ => hw0 q
    obtain ⟨hqF, hqn⟩ := Finset.mem_filter.mp hq
    exact hS q hqn ((hF q hqF).trans_le (le_abs_self _))
  · rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (summable_lorentzMassWTerm hL1 _).sum_le_tsum _
      fun q _ => lorentzMassWTerm_nonneg hL1 _ q
  · exact Finset.prod_nonneg fun q _ => (Real.exp_pos _).le
  · positivity

/-- The exponent bookkeeping with a cluster of size `M ≤ c(log 3 + ℓ)`. Here `ip` stands for
`1/π` and `w` is the cost per cluster copy. -/
theorem sparse_exponent_neg {D w M c u Cp lL lG l3 lp ℓ κ C N P ip : ℝ} (hκ : 0 < κ)
    (hip : 0 < ip) (hC : 0 ≤ C) (hw : 0 ≤ w) (hu0 : 0 ≤ u) (hu : u ≤ κ * ip / 4) (hℓ0 : 0 ≤ ℓ)
    (hc : c * (w + κ / 2) ≤ κ * ip / 8) (hM : M ≤ c * (l3 + ℓ)) (hN : P - M ≤ N)
    (hP : (2 * C + ip) * (ℓ - lp) - 2 * C * lG ≤ P) (hG : lG ≤ l3 + ℓ) (hLL : lL ≤ l3 + ℓ)
    (hℓ : D + u * (Cp + l3) + κ / 2 * ((2 * C + ip) * lp + 2 * C * l3) +
        c * (w + κ / 2) * l3 + κ * ip / 8 ≤ κ * ip / 8 * ℓ) :
    D + w * M + u * (Cp + lL) - κ / 2 * N < 0 := by
  have h1 := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ κ / 2)
  have h2 := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ κ / 2)
  have h3 := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ κ * C)
  have h4 := mul_le_mul_of_nonneg_left hLL hu0
  have h5 := mul_le_mul_of_nonneg_right hu hℓ0
  have h6 := mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ w + κ / 2)
  have h7 := mul_le_mul_of_nonneg_right hc hℓ0
  have h8 : 0 < κ * ip := mul_pos hκ hip
  nlinarith

/-- A set all of whose finite parts have at most `B` elements is finite. -/
theorem finite_of_forall_finset_card_le {α : Type*} {S : Set α} {B : ℝ}
    (hS : ∀ G : Finset α, (∀ q ∈ G, q ∈ S) → (G.card : ℝ) ≤ B) : S.Finite := by
  by_contra hinf
  obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈B⌉₊ + 1)
  have := hS t fun q hq => ht hq
  rw [htc] at this
  push_cast at this
  linarith [Nat.le_ceil B]

/-- **Only dense clusters mask the cosine producer.** For `h, r, s₀ > 0` there are `L, c > 0` and
`T₀` such that: if `ζ₀ = γ₀ + iδ` with `γ₀ ≥ T₀`, `η ≥ 0`, `η + h + r + s₀ ≤ δ`, and every finite
family of copies within horizontal distance `L` with `|Im| > η` has at most `c log γ₀` members, then
`cos(hD)Ξ` vanishes within `r` of `ζ₀ − ih`, above height `η`. -/
theorem exists_zero_cosShiftXi_of_sparseCluster {h r s₀ : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hs₀ : 0 < s₀) :
    ∃ L c T₀ : ℝ, 0 < L ∧ 0 < c ∧ ∀ (q₀ : XiZeroCopy) (η : ℝ), 0 ≤ η →
      η + h + r + s₀ ≤ (xiSpectralPoint q₀).im → T₀ ≤ (xiSpectralPoint q₀).re →
      (∀ G : Finset XiZeroCopy, (∀ q ∈ G,
        |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ L ∧ η < |(xiSpectralPoint q).im|) →
          (G.card : ℝ) ≤ c * Real.log (xiSpectralPoint q₀).re) →
      ∃ z, ‖z - (xiSpectralPoint q₀ - h * I)‖ ≤ r ∧ η < z.im ∧ cosShiftXi h z = 0 := by
  classical
  obtain ⟨C, T₁, hC, hT₁, hwin⟩ := exists_window_lower_count
  have hpi := Real.pi_pos
  set ip := Real.pi⁻¹ with hip_def
  have hip : 0 < ip := inv_pos.mpr hpi
  set H := 2 * Real.pi * C + 1 with hH
  have hH0 : 0 < H := by positivity
  have hHpi : H / Real.pi = 2 * C + ip := by rw [hH, hip_def]; field_simp
  set κ₀ := 4 * h * s₀ / ((H + r) ^ 2 + (1 + r) ^ 2) with hκ₀
  have hκ₀0 : 0 < κ₀ := by positivity
  have hpos : 0 ≤ 256 * h / (κ₀ * ip) := by positivity
  set L := H + 2 * r + 1 + 256 * h / (κ₀ * ip) with hL
  have hhL : 256 * h / (κ₀ * ip) ≤ L := by rw [hL]; linarith
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  have hL0 : 0 < L := by linarith
  have h2rL : 2 * r ≤ L := by rw [hL]; linarith
  have hHL : H ≤ L := by rw [hL]; linarith
  set u := 64 * h / L with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hu : u ≤ κ₀ * ip / 4 := by
    rw [hu_def, div_le_iff₀ hL0]
    have h1 := mul_le_mul_of_nonneg_left hhL (by positivity : (0 : ℝ) ≤ κ₀ * ip / 4)
    have h2 : κ₀ * ip / 4 * (256 * h / (κ₀ * ip)) = 64 * h := by field_simp; ring
    linarith
  set K₁ := 3 * Real.sqrt (r / 2) / (r / 2) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set w := 2 * Real.sqrt (2 * h) * K₁ with hw
  have hw0 : 0 ≤ w := by positivity
  set c := κ₀ * ip / (8 * (w + κ₀ / 2)) with hc
  have hc0 : 0 < c := by positivity
  have hcw : c * (w + κ₀ / 2) ≤ κ₀ * ip / 8 := by
    rw [hc]; rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 < w + κ₀ / 2 := by positivity
    nlinarith
  set cf := 1 + 4 * h / r with hcf
  have hcf0 : 0 < cf := by positivity
  set D := Real.log cf with hD
  set Cp := xiLineTwoLogDerivConstant
  set A := D + u * (Cp + Real.log 3) +
    κ₀ / 2 * ((2 * C + ip) * Real.log (2 * Real.pi) + 2 * C * Real.log 3) +
    c * (w + κ₀ / 2) * Real.log 3 + κ₀ * ip / 8 with hA
  refine ⟨L, c, T₁ + L + 4 + 4 * H + Real.exp (A / (κ₀ * ip / 8)), hL0, hc0,
    fun q₀ η hη hdepth hT hclu => ?_⟩
  set ζ₀ := xiSpectralPoint q₀ with hζ₀_def
  set γ₀ := ζ₀.re with hγ₀
  have hexp0 := Real.exp_pos (A / (κ₀ * ip / 8))
  have hγH : T₁ ≤ γ₀ - H := by linarith
  have hγpos : 0 < γ₀ - H := by linarith
  have hγ0 : 0 < γ₀ := by linarith
  have hδ : ζ₀.im ≤ 1 / 2 := (le_abs_self _).trans (abs_xiSpectralPoint_im_le q₀)
  -- the cluster as a finite set
  set Sset : Set XiZeroCopy :=
    {q | |(xiSpectralPoint q).re - γ₀| ≤ L ∧ η < |(xiSpectralPoint q).im|} with hSset
  have hSfin : Sset.Finite := finite_of_forall_finset_card_le fun G hG => hclu G hG
  set S := hSfin.toFinset with hS_def
  have hmemS : ∀ q, |(xiSpectralPoint q).re - γ₀| ≤ L → η < |(xiSpectralPoint q).im| → q ∈ S :=
    fun q h1 h2 => (Set.Finite.mem_toFinset hSfin).mpr ⟨h1, h2⟩
  have hScard : (S.card : ℝ) ≤ c * Real.log γ₀ :=
    hclu S fun q hq => (Set.Finite.mem_toFinset hSfin).mp hq
  -- the radius
  obtain ⟨r', ⟨hr'1, hr'2⟩, hsep, hsum⟩ :=
    exists_mem_Icc_sum_rpow_le S (fun q => ‖xiSpectralPoint q - ζ₀‖) hr
  have hr'0 : 0 < r' := by linarith
  -- the window of neighbours
  obtain ⟨P, hPwin, hPcard⟩ := hwin γ₀ H hH0.le hγH
  set Nb := P.filter fun q => |(xiSpectralPoint q).im| ≤ η with hNb_def
  have hPre : ∀ q ∈ P, |(xiSpectralPoint q).re - γ₀| ≤ H := by
    intro q hq
    obtain ⟨h1, h2⟩ := hPwin q hq
    rw [xiSpectralPoint_re_eq_ordinate, abs_le]
    constructor <;> linarith
  have hNcard : (P.card : ℝ) - S.card ≤ Nb.card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := P)
      (fun q => |(xiSpectralPoint q).im| ≤ η)
    have hb : (P.filter fun q => ¬ |(xiSpectralPoint q).im| ≤ η).card ≤ S.card := by
      refine Finset.card_le_card fun q hq => ?_
      obtain ⟨hqP, hqn⟩ := Finset.mem_filter.mp hq
      exact hmemS q ((hPre q hqP).trans hHL) (not_le.mp hqn)
    have : P.card ≤ S.card + Nb.card := by rw [hNb_def]; omega
    have : (P.card : ℝ) ≤ S.card + Nb.card := by exact_mod_cast this
    linarith
  -- the exceptional set
  set Exc : Set XiZeroCopy := {q | q ≠ q₀ ∧ η < (xiSpectralPoint q).im} with hExc
  have hzim : ∀ z ∈ sphere (ζ₀ - h * I) r', 0 ≤ z.im := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have h1 := Complex.abs_im_le_norm (z - (ζ₀ - h * I))
    rw [hz] at h1
    have e : (z - (ζ₀ - h * I)).im = z.im - (ζ₀.im - h) := by simp
    rw [e, abs_le] at h1
    linarith
  set B := Real.exp (2 * Real.sqrt (2 * h) *
      ∑ q ∈ S, |r' - ‖xiSpectralPoint q - ζ₀‖| ^ (-(1 / 2) : ℝ)) *
    Real.exp (8 * h * lorentzMassW L γ₀) with hB
  have hprod := fun (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, q ∈ Exc) (z : ℂ)
      (hz : z ∈ sphere (ζ₀ - h * I) r') =>
    prod_shift_le_of_sparse (η := η) (L := L) hh.le hr'0.le (by linarith) hL1 S hmemS
      (fun q hq => hsep q hq) F (fun q hq => (hF q hq).2)
      (by rwa [mem_sphere, dist_eq_norm] at hz) (hzim z hz)
  have hB0 : 0 ≤ B := by positivity
  have hNbP : ∀ q ∈ Nb, q ≠ q₀ ∧ q ∉ Exc ∧
      |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ H ∧ -η ≤ (xiSpectralPoint q).im := by
    intro q hq
    obtain ⟨hqP, hqs⟩ := Finset.mem_filter.mp hq
    rw [abs_le] at hqs
    refine ⟨fun h' => ?_, fun h' => absurd hqs.2 (not_le.mpr h'.2), hPre q hqP, hqs.1⟩
    rw [h'] at hqs
    linarith [hqs.2]
  have hcrowd : (2 * h + r') / r' * B *
      Real.sqrt (1 - crowdKappa (xiSpectralPoint q₀) h r' η H) ^ Nb.card < 1 := by
    have hκ : κ₀ ≤ crowdKappa ζ₀ h r' η H :=
      crowdKappa_ge_of_le hh.le hr'0.le hr'2 hη hH0.le hs₀ hdepth hδ
    have hsq : Real.sqrt (1 - crowdKappa ζ₀ h r' η H) ≤ Real.exp (-κ₀ / 2) := by
      have h1 : 1 - crowdKappa ζ₀ h r' η H ≤ Real.exp (-κ₀) := by
        have := Real.add_one_le_exp (-κ₀)
        linarith
      have h2 : Real.exp (-κ₀) = Real.exp (-κ₀ / 2) ^ 2 := by
        rw [sq, ← Real.exp_add]; ring_nf
      calc Real.sqrt (1 - crowdKappa ζ₀ h r' η H) ≤ Real.sqrt (Real.exp (-κ₀)) :=
            Real.sqrt_le_sqrt h1
        _ = Real.exp (-κ₀ / 2) := by rw [h2, Real.sqrt_sq (Real.exp_pos _).le]
    have hpow : Real.sqrt (1 - crowdKappa ζ₀ h r' η H) ^ Nb.card ≤
        Real.exp ((Nb.card : ℝ) * (-κ₀ / 2)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq _
    have hmass := lorentzMassW_le_log hL1 γ₀
    rw [abs_of_pos hγ0] at hmass
    have hlead : (2 * h + r') / r' ≤ cf := lead_le hh.le hr hr'1
    have hclus : 2 * Real.sqrt (2 * h) *
        ∑ q ∈ S, |r' - ‖xiSpectralPoint q - ζ₀‖| ^ (-(1 / 2) : ℝ) ≤ w * S.card := by
      calc 2 * Real.sqrt (2 * h) *
            ∑ q ∈ S, |r' - ‖xiSpectralPoint q - ζ₀‖| ^ (-(1 / 2) : ℝ)
          ≤ 2 * Real.sqrt (2 * h) * (S.card * K₁) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = w * S.card := by rw [hw]; ring
    set lL := Real.log (L + γ₀ + 4)
    set ℓ := Real.log (γ₀ - H) with hℓ_def
    have hℓbig : A / (κ₀ * ip / 8) ≤ ℓ := by
      rw [hℓ_def, Real.le_log_iff_exp_le hγpos]
      linarith
    have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
    have hl3 : Real.log 3 + ℓ = Real.log (3 * (γ₀ - H)) := by
      rw [Real.log_mul (by norm_num) hγpos.ne']
    have hG : Real.log (γ₀ + H) ≤ Real.log 3 + ℓ := by
      rw [hl3]; exact Real.log_le_log (by linarith) (by linarith)
    have hLL : lL ≤ Real.log 3 + ℓ := by
      rw [hl3]; exact Real.log_le_log (by linarith) (by linarith)
    have hlg : Real.log γ₀ ≤ Real.log 3 + ℓ := by
      rw [hl3]; exact Real.log_le_log hγ0 (by linarith)
    have hM : (S.card : ℝ) ≤ c * (Real.log 3 + ℓ) :=
      hScard.trans (mul_le_mul_of_nonneg_left hlg hc0.le)
    have hPc : (2 * C + ip) * (ℓ - Real.log (2 * Real.pi)) - 2 * C * Real.log (γ₀ + H) ≤
        P.card := by
      rw [← hHpi]; exact hPcard
    have hℓA : A ≤ κ₀ * ip / 8 * ℓ := by
      have h1 := mul_le_mul_of_nonneg_left hℓbig (by positivity : (0 : ℝ) ≤ κ₀ * ip / 8)
      rwa [mul_div_cancel₀ _ (by positivity : κ₀ * ip / 8 ≠ 0)] at h1
    have hE := sparse_exponent_neg (D := D) (Cp := Cp) (lL := lL) hκ₀0 hip hC.le hw0 hu0 hu hℓ0
      hcw hM hNcard hPc hG hLL (by rw [hA] at hℓA; linarith)
    have hmass' : 8 * h * lorentzMassW L γ₀ ≤ u * (Cp + lL) := by
      have := mul_le_mul_of_nonneg_left hmass (by positivity : (0 : ℝ) ≤ 8 * h)
      have e : 8 * h * (8 / L * (Cp + Real.log (L + γ₀ + 4))) = u * (Cp + lL) := by
        rw [hu_def]; field_simp; ring
      linarith
    have hcpow : cf * Real.exp (w * S.card) = Real.exp (D + w * S.card) := by
      rw [hD, Real.exp_add, Real.exp_log hcf0]
    have hsq0 : 0 ≤ Real.sqrt (1 - crowdKappa ζ₀ h r' η H) ^ Nb.card := by positivity
    have hlead0 : 0 ≤ (2 * h + r') / r' := by positivity
    calc (2 * h + r') / r' * B * Real.sqrt (1 - crowdKappa ζ₀ h r' η H) ^ Nb.card
        ≤ cf * (Real.exp (w * S.card) * Real.exp (8 * h * lorentzMassW L γ₀)) *
            Real.exp ((Nb.card : ℝ) * (-κ₀ / 2)) := by
          refine mul_le_mul (mul_le_mul hlead ?_ hB0 hcf0.le) hpow hsq0
            (mul_nonneg hcf0.le (by positivity))
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hclus) (Real.exp_pos _).le
      _ = Real.exp (D + w * S.card + 8 * h * lorentzMassW L γ₀ - κ₀ / 2 * Nb.card) := by
          rw [← mul_assoc, hcpow, ← Real.exp_add, ← Real.exp_add]
          ring_nf
      _ < 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by linarith only [hE, hmass'])
  have hgap : η + r' < (xiSpectralPoint q₀).im - h := by
    linarith only [hdepth, hr'2, hs₀]
  have hclass : ∀ q, q ≠ q₀ → q ∉ Exc → (xiSpectralPoint q).im ≤ η :=
    fun q hq hq' => not_lt.mp fun hlt => hq' ⟨hq, hlt⟩
  have hExcne : ∀ q ∈ Exc, ∀ z ∈ sphere (xiSpectralPoint q₀ - h * I) r',
      z + h * I ≠ xiSpectralPoint q := fun q hq z hz =>
    (hprod {q} (by simpa using hq) z hz).2 q (Finset.mem_singleton_self q)
  have hExcB : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, q ∈ Exc) →
      ∀ z ∈ sphere (xiSpectralPoint q₀ - h * I) r',
        (F.val.map fun q => ‖z - h * I - xiSpectralPoint q‖).prod ≤
          B * (F.val.map fun q => ‖z + h * I - xiSpectralPoint q‖).prod := by
    intro F hF z hz
    rw [hB]
    exact (hprod F hF z hz).1
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_zero_cosShiftXi_of_exceptionalSet hh hr'0 hη hB0 hgap
    (fun h' => h'.1 rfl) hclass hExcne hExcB hNbP hcrowd
  exact ⟨z, hz1.trans hr'2, hz2, hz3⟩

/-- **Off-line sparsity** (Backlund's form of the Lindelöf hypothesis): for every `η, L, c > 0`, at
all large heights `t` every finite family of copies within horizontal distance `L` of `t` with
`|Im| > η` has at most `c log t` members. -/
def OffLineSparse : Prop :=
  ∀ η L c : ℝ, 0 < η → 0 < L → 0 < c → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ G : Finset XiZeroCopy,
    (∀ q ∈ G, |(xiSpectralPoint q).re - t| ≤ L ∧ η < |(xiSpectralPoint q).im|) →
      (G.card : ℝ) ≤ c * Real.log t

/-- **A real-rooted cosine level is an eventual strip under off-line sparsity.** If off-line zeros
are sparse in Backlund's sense and `cos(hD)Ξ` has only real zeros, then for every `ε > 0` all zeros
of large height satisfy `Im ζ ≤ h + ε`, i.e. `β ≥ ½ − h − ε`. -/
theorem eventually_im_le_of_cosShiftXi_real_of_sparse (hsp : OffLineSparse) {h : ℝ} (hh : 0 < h)
    (hreal : ∀ z, cosShiftXi h z = 0 → z.im = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ q : XiZeroCopy, T ≤ (xiSpectralPoint q).re → (xiSpectralPoint q).im ≤ h + ε := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨L, c, T₀, hL, hc, hmain⟩ := exists_zero_cosShiftXi_of_sparseCluster hh hε3 hε3
  obtain ⟨T, hT⟩ := hsp (ε / 3) L c hε3 hL hc
  refine ⟨max T₀ T, fun q₀ hq₀ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨z, -, hz, hz0⟩ := hmain q₀ (ε / 3) hε3.le (by linarith) (le_of_max_le_left hq₀)
    (hT _ (le_of_max_le_right hq₀))
  have := hreal z hz0
  linarith

end

end RHTower.CosineSparseCluster
