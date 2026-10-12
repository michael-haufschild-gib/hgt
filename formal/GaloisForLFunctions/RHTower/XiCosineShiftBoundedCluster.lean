import GaloisForLFunctions.RHTower.XiCosineShiftIsolatedDeepZero

/-!
# Bounded clusters of deep zeros never mask the cosine producer at large height

Let `ζ₀ = γ₀ + iδ` be the spectral point of a zero copy of `ξ`, and let `h, r, s₀ > 0`.

**Theorem** (`exists_zero_cosShiftXi_of_boundedCluster`). There is a window `L > 0`, depending only
on `h, r, s₀`, such that for every `M` there is a height `T₀` with the following property. Suppose
`γ₀ ≥ T₀`, `η ≥ 0` and `η + h + r + s₀ ≤ δ`, and suppose at most `M` copies of horizontal distance
at most `L` from `ζ₀` have `|Im| > η`. Then `cos(hD)Ξ` vanishes within `r` of `ζ₀ − ih`, at a point
with imaginary part above `η`.

**Corollary** (`exists_large_cluster_of_cosShiftXi_real`). If `cos(hD)Ξ` has only real zeros, then
at large height every zero of depth `≥ η + h + r + s₀` has more than `M` copies with `|Im| > η`
within the fixed window `L`. So a real-rooted cosine level `h` below the depth of an off-line zero
needs deep clusters whose size tends to infinity with the height.

For polynomials, bounded clusters do shield. For example `cos(hD)(z² + δ²)²` is real-rooted for
`h ≥ δ/√2`. At large height the Riemann–von Mangoldt crowd of `≍ log γ₀` shallow neighbours
removes this.

**Proof.** First choose the radius. Of the `M + 1` midpoints `r/2 + (2k+1)r/(4(M+1))` in `[r/2, r]`,
one is at distance `≥ r/(4(M+1))` from every distance `|ζ − ζ₀|` of a near deep copy. Two midpoints
cannot share a near copy, so pigeonhole applies. On the circle of that radius, every near deep copy
changes the modulus across the shift by at most `1 + 8h(M+1)/r`. Far deep copies are paid by the
width-`L` Lorentzian mass, as in the isolated case. The window count is reduced by at most `M`.
-/

open Complex ComplexConjugate Filter Topology Set Polynomial Metric

namespace RHTower.CosineBoundedCluster

open GaloisForLFunctions.HTGeometry RHTower.DeBruijn RHTower.CosineDefectBudget
  RHTower.CrowdedPersistence RHTower.CosineCrowdedPersistence RHTower.CosineIsolatedDeepZero

noncomputable section

/-! ## Choice of the radius -/

/-- **Pigeonhole radius.** If every finite part of `S` has at most `M` elements, some radius
`r' ∈ [r/2, r]` is at distance at least `r/(4(M+1))` from every value `a i`, `i ∈ S`. -/
theorem exists_radius_separated {ι : Type*} {S : Set ι} {M : ℕ} (a : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hS : ∀ G : Finset ι, (∀ i ∈ G, i ∈ S) → G.card ≤ M) :
    ∃ r', r / 2 ≤ r' ∧ r' ≤ r ∧ ∀ i ∈ S, r / (4 * (M + 1)) ≤ |r' - a i| := by
  classical
  set ε := r / (4 * (M + 1)) with hε
  have hM : (0 : ℝ) < M + 1 := by positivity
  have hε0 : 0 < ε := by positivity
  set m : ℕ → ℝ := fun k => r / 2 + (2 * k + 1) * ε with hm
  by_contra hcon
  have hbad : ∀ k ∈ Finset.range (M + 1), ∃ i ∈ S, |m k - a i| < ε := by
    intro k hk
    by_contra hk'
    apply hcon
    have hk1 : (k : ℝ) + 1 ≤ M + 1 := by
      have := Finset.mem_range.mp hk
      exact_mod_cast this
    have hεM : (M + 1 : ℝ) * ε = r / 4 := by rw [hε]; field_simp
    refine ⟨m k, ?_, ?_, fun i hi => ?_⟩
    · simp only [hm]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    · simp only [hm]; nlinarith
    · by_contra hlt
      exact hk' ⟨i, hi, not_le.mp hlt⟩
  haveI : Nonempty ι := ⟨(hbad 0 (by simp)).choose⟩
  choose! g hgS hg using hbad
  have hinj : Set.InjOn g (Finset.range (M + 1) : Set ℕ) := by
    intro k hk k' hk' hkk
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(k : ℝ) - k'| := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
        exact le_abs.mpr (Or.inr (by linarith))
      · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
        exact le_abs.mpr (Or.inl (by linarith))
    have h2 := hg k hk
    have h3 := hg k' hk'
    rw [hkk] at h2
    have h4 : |m k - m k'| < 2 * ε := by
      calc |m k - m k'| = |(m k - a (g k')) - (m k' - a (g k'))| := by ring_nf
        _ ≤ |m k - a (g k')| + |m k' - a (g k')| := abs_sub _ _
        _ < 2 * ε := by linarith
    have h5 : m k - m k' = 2 * ε * ((k : ℝ) - k') := by simp only [hm]; ring
    rw [h5, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ε)] at h4
    nlinarith
  have hG := hS ((Finset.range (M + 1)).image g) fun i hi => by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    exact hgS k hk
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hG
  omega

/-- **A separated near copy.** On the circle `|z − (ζ₀ − ih)| = r'`, a copy `ζ` with
`||ζ − ζ₀| − r'| ≥ ε` changes the modulus across the shift by at most `1 + 2h/ε`. -/
theorem norm_shift_le_of_separated {z ζ ζ₀ : ℂ} {h r' ε : ℝ} (hh : 0 ≤ h) (hε : 0 < ε)
    (hz : ‖z - (ζ₀ - h * I)‖ = r') (hsep : ε ≤ |r' - ‖ζ - ζ₀‖|) :
    ‖z - h * I - ζ‖ ≤ (1 + 2 * h / ε) * ‖z + h * I - ζ‖ ∧ 0 < ‖z + h * I - ζ‖ := by
  have hb : ε ≤ ‖z + h * I - ζ‖ := by
    have e : z + h * I - ζ = (z - (ζ₀ - h * I)) - (ζ - ζ₀) := by ring
    rw [e]
    refine hsep.trans ?_
    rw [← hz]
    exact abs_norm_sub_norm_le _ _
  refine ⟨?_, hε.trans_le hb⟩
  have e2 : z - h * I - ζ = (z + h * I - ζ) - ((2 * h : ℝ) : ℂ) * I := by push_cast; ring
  have hI : ‖((2 * h : ℝ) : ℂ) * I‖ = 2 * h := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  rw [e2]
  have h1 := norm_sub_le (z + h * I - ζ) (((2 * h : ℝ) : ℂ) * I)
  rw [hI] at h1
  have h2 : 2 * h ≤ 2 * h / ε * ‖z + h * I - ζ‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]
    exact mul_le_mul_of_nonneg_left hb (by linarith)
  nlinarith

/-- **The exceptional product for a bounded cluster.** -/
theorem prod_shift_le_of_cluster {q₀ : XiZeroCopy} {η h r' L ε : ℝ} {M : ℕ} (hh : 0 ≤ h)
    (hr' : 0 ≤ r') (hL : 2 * r' ≤ L) (hL1 : 1 ≤ L) (hε : 0 < ε)
    (hclu : ∀ G : Finset XiZeroCopy, (∀ q ∈ G,
      |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ L ∧ η < |(xiSpectralPoint q).im|) →
        G.card ≤ M)
    (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, η < (xiSpectralPoint q).im) {z : ℂ}
    (hz : ‖z - (xiSpectralPoint q₀ - h * I)‖ = r') (hzim : 0 ≤ z.im)
    (hsep : ∀ q, |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ L →
      η < |(xiSpectralPoint q).im| → ε ≤ |r' - ‖xiSpectralPoint q - xiSpectralPoint q₀‖|) :
    (F.val.map fun q => ‖z - h * I - xiSpectralPoint q‖).prod ≤
        (1 + 2 * h / ε) ^ M * Real.exp (8 * h * lorentzMassW L (xiSpectralPoint q₀).re) *
          (F.val.map fun q => ‖z + h * I - xiSpectralPoint q‖).prod ∧
      ∀ q ∈ F, z + h * I ≠ xiSpectralPoint q := by
  classical
  set ζ₀ := xiSpectralPoint q₀ with hζ₀_def
  set c := 1 + 2 * h / ε with hc
  have hc1 : 1 ≤ c := by rw [hc]; have : 0 ≤ 2 * h / ε := by positivity
                         linarith
  have hL0 : 0 < L := by linarith
  set near : XiZeroCopy → Prop := fun q => |(xiSpectralPoint q).re - ζ₀.re| ≤ L with hnear
  set f : XiZeroCopy → ℝ := fun q =>
    if near q then c else Real.exp (8 * h * lorentzMassWTerm L ζ₀.re q) with hf
  have hone : ∀ q ∈ F, ‖z - h * I - xiSpectralPoint q‖ ≤ f q * ‖z + h * I - xiSpectralPoint q‖ ∧
      0 < ‖z + h * I - xiSpectralPoint q‖ := by
    intro q hq
    have hdeep : η < |(xiSpectralPoint q).im| := (hF q hq).trans_le (le_abs_self _)
    by_cases hn : near q
    · simp only [hf, hn, if_true]
      exact norm_shift_le_of_separated hh hε hz (hsep q hn hdeep)
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
  rw [hf, Finset.prod_ite, Finset.prod_const]
  apply mul_le_mul
  · refine pow_le_pow_right₀ hc1 (hclu _ fun q hq => ?_)
    obtain ⟨hqF, hqn⟩ := Finset.mem_filter.mp hq
    exact ⟨hqn, (hF q hqF).trans_le (le_abs_self _)⟩
  · rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (summable_lorentzMassWTerm hL1 _).sum_le_tsum _
      fun q _ => lorentzMassWTerm_nonneg hL1 _ q
  · exact Finset.prod_nonneg fun q _ => (Real.exp_pos _).le
  · positivity

/-- The crowding constant at a radius `r' ≤ r` is bounded below by the one at `r`. -/
theorem crowdKappa_ge_of_le {ζ₀ : ℂ} {h r r' η H s₀ : ℝ} (hh : 0 ≤ h) (hr' : 0 ≤ r') (hrr : r' ≤ r)
    (hη : 0 ≤ η) (hH : 0 ≤ H) (hs₀ : 0 < s₀) (hd : η + h + r + s₀ ≤ ζ₀.im) (hδ : ζ₀.im ≤ 1 / 2) :
    4 * h * s₀ / ((H + r) ^ 2 + (1 + r) ^ 2) ≤ crowdKappa ζ₀ h r' η H := by
  refine le_trans ?_ (crowdKappa_ge hh hr' hη hs₀ (by linarith) hδ)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have h1 : H + r' ≤ H + r := by linarith
  have h2 : 1 + r' ≤ 1 + r := by linarith
  have := pow_le_pow_left₀ (by linarith) h1 2
  have := pow_le_pow_left₀ (by linarith) h2 2
  linarith

/-- The centre factor at a radius `r' ≥ r/2`. -/
theorem lead_le {h r r' : ℝ} (hh : 0 ≤ h) (hr : 0 < r) (hr' : r / 2 ≤ r') :
    (2 * h + r') / r' ≤ 1 + 4 * h / r := by
  have hr'0 : 0 < r' := by linarith
  rw [div_le_iff₀ hr'0, add_mul, one_mul, div_mul_eq_mul_div]
  have : 2 * h ≤ 4 * h * r' / r := by
    rw [le_div_iff₀ hr]
    nlinarith
  linarith

/-! ## Bounded clusters at large height -/

/-- **Bounded clusters never mask the cosine producer at large height.** For `h, r, s₀ > 0` there
is a window `L > 0` such that for every `M` there is `T₀` with the following property. Let `q₀` be a
copy with `ζ₀ = γ₀ + iδ`, `γ₀ ≥ T₀`, and let `η ≥ 0`, `η + h + r + s₀ ≤ δ`. If at most `M` copies
of horizontal distance at most `L` from `ζ₀` have `|Im| > η`, then `cos(hD)Ξ` vanishes within `r` of
`ζ₀ − ih`, at a point with imaginary part above `η`. -/
theorem exists_zero_cosShiftXi_of_boundedCluster {h r s₀ : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hs₀ : 0 < s₀) :
    ∃ L : ℝ, 0 < L ∧ ∀ M : ℕ, ∃ T₀ : ℝ, ∀ (q₀ : XiZeroCopy) (η : ℝ), 0 ≤ η →
      η + h + r + s₀ ≤ (xiSpectralPoint q₀).im → T₀ ≤ (xiSpectralPoint q₀).re →
      (∀ G : Finset XiZeroCopy, (∀ q ∈ G,
        |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ L ∧ η < |(xiSpectralPoint q).im|) →
          G.card ≤ M) →
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
  refine ⟨L, hL0, fun M => ?_⟩
  set ε := r / (4 * (M + 1)) with hε
  have hε0 : 0 < ε := by positivity
  set cf := 1 + 4 * h / r with hcf
  have hcf0 : 0 < cf := by positivity
  set nf := 1 + 2 * h / ε with hnf
  have hnf0 : 0 < nf := by positivity
  set D := Real.log cf + M * Real.log nf with hD
  set Cp := xiLineTwoLogDerivConstant
  set A := D + u * (Cp + Real.log 3) +
    κ₀ / 2 * ((2 * C + ip) * Real.log (2 * Real.pi) + 2 * C * Real.log 3 + M) + κ₀ * ip / 4
    with hA
  refine ⟨T₁ + L + 4 + 4 * H + Real.exp (A / (κ₀ * ip / 4)),
    fun q₀ η hη hdepth hT hclu => ?_⟩
  set ζ₀ := xiSpectralPoint q₀ with hζ₀_def
  set γ₀ := ζ₀.re with hγ₀
  have hexp0 := Real.exp_pos (A / (κ₀ * ip / 4))
  have hγH : T₁ ≤ γ₀ - H := by linarith
  have hγpos : 0 < γ₀ - H := by linarith
  have hγ0 : 0 < γ₀ := by linarith
  have hδ : ζ₀.im ≤ 1 / 2 := (le_abs_self _).trans (abs_xiSpectralPoint_im_le q₀)
  -- the radius
  obtain ⟨r', hr'1, hr'2, hsep⟩ := exists_radius_separated (M := M)
    (S := {q | |(xiSpectralPoint q).re - γ₀| ≤ L ∧ η < |(xiSpectralPoint q).im|})
    (fun q => ‖xiSpectralPoint q - ζ₀‖) hr fun G hG => hclu G hG
  have hr'0 : 0 < r' := by linarith
  -- the window of neighbours
  obtain ⟨P, hPwin, hPcard⟩ := hwin γ₀ H hH0.le hγH
  set Nb := P.filter fun q => |(xiSpectralPoint q).im| ≤ η with hNb_def
  have hPre : ∀ q ∈ P, |(xiSpectralPoint q).re - γ₀| ≤ H := by
    intro q hq
    obtain ⟨h1, h2⟩ := hPwin q hq
    rw [xiSpectralPoint_re_eq_ordinate, abs_le]
    constructor <;> linarith
  have hNcard : (P.card : ℝ) - M ≤ Nb.card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := P)
      (fun q => |(xiSpectralPoint q).im| ≤ η)
    have hb : (P.filter fun q => ¬ |(xiSpectralPoint q).im| ≤ η).card ≤ M :=
      hclu _ fun q hq => by
        obtain ⟨hqP, hqn⟩ := Finset.mem_filter.mp hq
        exact ⟨(hPre q hqP).trans hHL, not_le.mp hqn⟩
    have : P.card ≤ M + Nb.card := by rw [hNb_def]; omega
    have : (P.card : ℝ) ≤ M + Nb.card := by exact_mod_cast this
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
  set B := nf ^ M * Real.exp (8 * h * lorentzMassW L γ₀) with hB
  have hprod := fun (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, q ∈ Exc) (z : ℂ)
      (hz : z ∈ sphere (ζ₀ - h * I) r') =>
    prod_shift_le_of_cluster (M := M) (L := L) (η := η) hh.le hr'0.le (by linarith) hL1 hε0
      hclu F (fun q hq => (hF q hq).2) (by rwa [mem_sphere, dist_eq_norm] at hz) (hzim z hz)
      fun q hq1 hq2 => hsep q ⟨hq1, hq2⟩
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
    have hcpow : cf * nf ^ M = Real.exp D := by
      rw [hD, Real.exp_add, Real.exp_nat_mul, Real.exp_log hcf0, Real.exp_log hnf0]
    set lL := Real.log (L + γ₀ + 4)
    set ℓ := Real.log (γ₀ - H) with hℓ_def
    have hℓbig : A / (κ₀ * ip / 4) ≤ ℓ := by
      rw [hℓ_def, Real.le_log_iff_exp_le hγpos]
      linarith
    have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
    have hl3 : Real.log 3 + ℓ = Real.log (3 * (γ₀ - H)) := by
      rw [Real.log_mul (by norm_num) hγpos.ne']
    have hG : Real.log (γ₀ + H) ≤ Real.log 3 + ℓ := by
      rw [hl3]; exact Real.log_le_log (by linarith) (by linarith)
    have hLL : lL ≤ Real.log 3 + ℓ := by
      rw [hl3]; exact Real.log_le_log (by linarith) (by linarith)
    have hPc : (2 * C + ip) * (ℓ - Real.log (2 * Real.pi)) - 2 * C * Real.log (γ₀ + H) ≤
        P.card := by
      rw [← hHpi]; exact hPcard
    have hℓA : A ≤ κ₀ * ip / 4 * ℓ := by
      have h1 := mul_le_mul_of_nonneg_left hℓbig (by positivity : (0 : ℝ) ≤ κ₀ * ip / 4)
      rwa [mul_div_cancel₀ _ (by positivity : κ₀ * ip / 4 ≠ 0)] at h1
    have hE := crowd_exponent_neg (D := D) (Cp := Cp) (lL := lL) hκ₀0 hip hC.le hu0 hu hℓ0
      hNcard hPc hG hLL (by rw [hA] at hℓA; linarith)
    have hmass' : 8 * h * lorentzMassW L γ₀ ≤ u * (Cp + lL) := by
      have := mul_le_mul_of_nonneg_left hmass (by positivity : (0 : ℝ) ≤ 8 * h)
      have e : 8 * h * (8 / L * (Cp + Real.log (L + γ₀ + 4))) = u * (Cp + lL) := by
        rw [hu_def]; field_simp; ring
      linarith
    calc (2 * h + r') / r' * B * Real.sqrt (1 - crowdKappa ζ₀ h r' η H) ^ Nb.card
        ≤ (cf * nf ^ M) * Real.exp (8 * h * lorentzMassW L γ₀) *
            Real.exp ((Nb.card : ℝ) * (-κ₀ / 2)) := by
          rw [hB, ← mul_assoc]
          apply mul_le_mul _ hpow (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hlead (by positivity)) (by positivity)
      _ = Real.exp (D + 8 * h * lorentzMassW L γ₀ - κ₀ / 2 * Nb.card) := by
          rw [hcpow, ← Real.exp_add, ← Real.exp_add]; ring_nf
      _ < 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_zero_cosShiftXi_of_exceptionalSet (Exc := Exc) (Nb := Nb)
    (H := H) (B := B) (r := r') hh hr'0 hη hB0 (by linarith) (fun h' => h'.1 rfl)
    (fun q hq hq' => by
      by_contra hlt
      exact hq' ⟨hq, not_le.mp hlt⟩)
    (fun q hq z hz => (hprod {q} (by simpa using hq) z hz).2 q (Finset.mem_singleton_self q))
    (fun F hF z hz => (hprod F hF z hz).1) hNbP hcrowd
  exact ⟨z, hz1.trans hr'2, hz2, hz3⟩

/-- **Real-rooted cosine levels force unbounded deep clusters.** If `cos(hD)Ξ` has only real zeros,
then for every `M`, at large height every copy of depth `≥ η + h + r + s₀` has more than `M` copies
with `|Im| > η` within the fixed horizontal window `L`. -/
theorem exists_large_cluster_of_cosShiftXi_real {h r s₀ : ℝ} (hh : 0 < h) (hr : 0 < r)
    (hs₀ : 0 < s₀) :
    ∃ L : ℝ, 0 < L ∧ ∀ M : ℕ, ∃ T₀ : ℝ, (∀ z, cosShiftXi h z = 0 → z.im = 0) →
      ∀ (q₀ : XiZeroCopy) (η : ℝ), 0 ≤ η → η + h + r + s₀ ≤ (xiSpectralPoint q₀).im →
        T₀ ≤ (xiSpectralPoint q₀).re →
        ∃ G : Finset XiZeroCopy, (∀ q ∈ G,
          |(xiSpectralPoint q).re - (xiSpectralPoint q₀).re| ≤ L ∧
            η < |(xiSpectralPoint q).im|) ∧ M < G.card := by
  obtain ⟨L, hL0, hL⟩ := exists_zero_cosShiftXi_of_boundedCluster hh hr hs₀
  refine ⟨L, hL0, fun M => ?_⟩
  obtain ⟨T₀, hT₀⟩ := hL M
  refine ⟨T₀, fun hreal q₀ η hη hd hT => ?_⟩
  by_contra hcon
  obtain ⟨z, -, hz, hz0⟩ := hT₀ q₀ η hη hd hT fun G hG => by
    by_contra hlt
    exact hcon ⟨G, hG, not_le.mp hlt⟩
  have := hreal z hz0
  linarith

end

end RHTower.CosineBoundedCluster
