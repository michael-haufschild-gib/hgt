import GaloisForLFunctions.ZeroConfigurationGeometry.SparseOnLineClustersNeverCancel

/-!
# Sparse clusters never cancel

`SparseOnLineClustersNeverCancel` reads every point of an on-line cluster of upper uniform
density `< 2a/π` with one pair of windows of aperture `a`. The same works for clusters of any
depths, counted as points of the configuration (an FE pair counts twice).

A point `w` of the cluster enters the pair image through `f̂(γ_w) conj ĝ(conj γ_w)`, with
`γ_w = (w − ½)/i` of imaginary part `½ − Re w ∈ [−½, ½]`. Match the heights of the cluster into
`D⁻¹ℤ` (Hall) and split by the parity of the lattice index. Let `f` vanish at `γ_w` on the even
half and `g` at `conj γ_w` on the odd half. Each half is a complex perturbation of `2D⁻¹ℤ` of
depth `≤ ½`, which windows of every aperture `> πD/2` blind
(`exists_window_blind_to_complex_perturbed_lattice`).

* **Blind windows from a complex matching**
  (`exists_window_blind_of_injOn_near_complex_lattice`).
* **The density criterion** (`eq_of_mimic_of_count_le`). Mimics at aperture `a` whose cluster has
  at most `D(y − x) + C` points at heights in every `[x, y]`, with `πD < 2a`, are equal, whatever
  the depths. The on-line lattice pair, whose cluster has density exactly `2a/π`, cancels
  (`exists_onLine_mimic_at_density`).

So a cancelling cluster has upper uniform density at least `2a/π`. This is the density of the
union of two lattices of spacing `π/a`, which is how the lattice pair cancels.
-/

open MeasureTheory Complex Set Filter
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- **Blind windows from a complex matching.** If the points `λ_i`, `i ∈ P`, of depth `≤ 1/2` are
matched injectively to lattice points `τ_i H` at distance `≤ L`, every aperture `> π/H` has a
window blind to them that sees any given `z₀` off them. -/
theorem exists_window_blind_of_injOn_near_complex_lattice {ι : Type*} (lam : ι → ℂ) (τ : ι → ℤ)
    (P : Set ι) (hτ : Set.InjOn τ P) {H L r : ℝ} (hH : 0 < H) (hr : π / H < r)
    (hL : ∀ i ∈ P, ‖lam i - τ i * H‖ ≤ L) (him : ∀ i ∈ P, |(lam i).im| ≤ 1 / 2) {z₀ : ℂ}
    (hz₀ : ∀ i ∈ P, z₀ ≠ lam i) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ i ∈ P, paperFT f (lam i) = 0) ∧ paperFT f z₀ ≠ 0 := by
  classical
  obtain ⟨c, ⟨hc0, hcH⟩, hcE⟩ := SquareRootThreshold.exists_mem_Ioo_notMem_of_countable hH
    (Set.countable_range fun k : ℤ => z₀.re - k * H)
  set ν : ℤ → ℂ := fun k => if hk : ∃ i ∈ P, τ i = k then lam hk.choose
    else ((k * H + c : ℝ) : ℂ) with hν
  have hνin : ∀ k (hk : ∃ i ∈ P, τ i = k), ν k = lam hk.choose := fun k hk => by
    simp only [hν, dif_pos hk]
  have hνout : ∀ k, (¬ ∃ i ∈ P, τ i = k) → ν k = ((k * H + c : ℝ) : ℂ) := fun k hk => by
    simp only [hν, dif_neg hk]
  have hντ : ∀ i ∈ P, ν (τ i) = lam i := fun i hi => by
    have hk : ∃ j ∈ P, τ j = τ i := ⟨i, hi, rfl⟩
    rw [hνin _ hk, hτ hk.choose_spec.1 hi hk.choose_spec.2]
  have hνb : ∀ k : ℤ, ‖ν k - k * H‖ ≤ |L| + H := by
    intro k
    by_cases hk : ∃ i ∈ P, τ i = k
    · obtain ⟨j, hjP, hjl, hj⟩ : ∃ j ∈ P, lam hk.choose = lam j ∧ τ j = k :=
        ⟨_, hk.choose_spec.1, rfl, hk.choose_spec.2⟩
      rw [hνin k hk, hjl, ← hj]
      exact (hL j hjP).trans (by linarith [le_abs_self L])
    · rw [hνout k hk, show ((k * H + c : ℝ) : ℂ) - k * H = (c : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
      linarith [abs_nonneg L]
  have hνim : ∀ k, |(ν k).im| ≤ 1 / 2 := by
    intro k
    by_cases hk : ∃ i ∈ P, τ i = k
    · rw [hνin k hk]; exact him _ hk.choose_spec.1
    · rw [hνout k hk, Complex.ofReal_im, abs_zero]; norm_num
  have hz₀' : ∀ k, z₀ ≠ ν k := by
    intro k hk0
    by_cases hk : ∃ i ∈ P, τ i = k
    · exact hz₀ hk.choose hk.choose_spec.1 (by rw [hk0, hνin k hk])
    · apply hcE
      refine ⟨k, ?_⟩
      have := congrArg Complex.re hk0
      rw [hνout k hk, Complex.ofReal_re] at this
      show z₀.re - k * H = c
      linarith
  obtain ⟨f, hf, hfν, hf0⟩ :=
    exists_window_blind_to_complex_perturbed_lattice hH hr ν hνb hνim hz₀'
  exact ⟨f, hf, fun i hi => by rw [← hντ i hi]; exact hfν (τ i), hf0⟩

theorem gammaOf_re (w : ℂ) : (gammaOf w).re = w.im := by
  rw [gammaOf, Complex.div_I]; simp

theorem gammaOf_im (w : ℂ) : (gammaOf w).im = -(w.re - 1 / 2) := by
  rw [gammaOf, Complex.div_I]; simp

/-- **Sparse clusters never cancel.** Mimics at aperture `a` whose cluster has at most
`D(y − x) + C` points at heights in every `[x, y]`, with `πD < 2a`, are equal, whatever the depths
of the points. -/
theorem eq_of_mimic_of_count_le {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {a D C : ℝ} (hD : 0 < D) (hDa : π * D < 2 * a)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ z.im ∈ Icc x y) → (s.card : ℝ) ≤ D * (y - x) + C) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  classical
  set S : Set ℂ := {z | multDiff Z Z' z ≠ 0} with hS
  set lam : S → ℝ := fun z => (z : ℂ).im with hlam
  have hcount' : ∀ (s : Finset S) (x y : ℝ), x ≤ y → (∀ i ∈ s, D * lam i ∈ Icc x y) →
      (s.card : ℝ) ≤ y - x + C := by
    intro s x y hxy hs
    have h := hcount (s.map (Function.Embedding.subtype _)) (x / D) (y / D)
      (div_le_div_of_nonneg_right hxy hD.le) fun z hz => by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
        obtain ⟨h1, h2⟩ := hs i hi
        refine ⟨i.2, (div_le_iff₀ hD).mpr ?_, (le_div_iff₀ hD).mpr ?_⟩
        · simp only [hlam] at h1; simp only [Function.Embedding.subtype_apply]; linarith
        · simp only [hlam] at h2; simp only [Function.Embedding.subtype_apply]; linarith
    rw [Finset.card_map] at h
    calc (s.card : ℝ) ≤ D * (y / D - x / D) + C := h
      _ = y - x + C := by field_simp
  obtain ⟨σ, hσ, hσd⟩ := exists_injective_near_int (fun i => D * lam i) hcount'
  set h := D⁻¹ with hh_def
  have hh : 0 < h := inv_pos.mpr hD
  have hDh : D * h = 1 := by rw [hh_def]; field_simp
  have hhalf : ∀ i : S, |lam i - ((σ i / 2 : ℤ) : ℝ) * (2 * h)| ≤ (C + 1) / 2 * h + h := by
    intro i
    have hmod := Int.emod_two_eq_zero_or_one (σ i)
    have hσi : |lam i - (σ i : ℝ) * h| ≤ (C + 1) / 2 * h := by
      have e : lam i - (σ i : ℝ) * h = h * (D * lam i - σ i) := by
        rw [mul_sub, ← mul_assoc, mul_comm h D, hDh, one_mul, mul_comm]
      rw [e, abs_mul, abs_of_pos hh, mul_comm]
      exact mul_le_mul_of_nonneg_right (hσd i) hh.le
    rcases hmod with h0 | h1
    · have e : ((σ i / 2 : ℤ) : ℝ) * (2 * h) = (σ i : ℝ) * h := by
        have : (2 : ℤ) * (σ i / 2) = σ i := by omega
        have hc : (2 : ℝ) * ((σ i / 2 : ℤ) : ℝ) = (σ i : ℝ) := by exact_mod_cast this
        linear_combination h * hc
      rw [e]
      linarith
    · have e : ((σ i / 2 : ℤ) : ℝ) * (2 * h) = (σ i : ℝ) * h - h := by
        have : (2 : ℤ) * (σ i / 2) + 1 = σ i := by omega
        have hc : (2 : ℝ) * ((σ i / 2 : ℤ) : ℝ) + 1 = (σ i : ℝ) := by exact_mod_cast this
        linear_combination h * hc
      rw [e, show lam i - ((σ i : ℝ) * h - h) = (lam i - (σ i : ℝ) * h) + h by ring]
      exact (abs_add_le _ _).trans (by rw [abs_of_pos hh]; linarith)
  have hr : π / (2 * h) < a := by
    rw [div_lt_iff₀ (by positivity)]
    have : a * (2 * h) = 2 * a / D := by rw [hh_def]; field_simp
    rw [this, lt_div_iff₀ hD]
    linarith
  -- the cluster lies in the strip
  have hstrip : ∀ i : S, |(i : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    intro i
    rcases mem_carrier_of_multDiff_ne_zero i.2 with h | h
    · obtain ⟨h1, h2⟩ := Z.strip _ h
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨h1, h2⟩ := Z'.strip _ h
      rw [abs_le]; constructor <;> linarith
  -- the camera points and their conjugates
  have hnorm : ∀ (w : ℂ) (t : ℝ), ‖w - t‖ ≤ |w.re - t| + |w.im| := fun w t => by
    have h := Complex.norm_le_abs_re_add_abs_im (w - t)
    simpa using h
  have hcast : ∀ i : S, ((σ i / 2 : ℤ) : ℂ) * ((2 * h : ℝ) : ℂ) =
      ((((σ i / 2 : ℤ) : ℝ) * (2 * h) : ℝ) : ℂ) := fun i => by push_cast; ring
  have hΓim : ∀ i : S, |(gammaOf (i : ℂ)).im| ≤ 1 / 2 := fun i => by
    rw [gammaOf_im, abs_neg]; exact hstrip i
  have hΓcim : ∀ i : S, |(conj (gammaOf (i : ℂ))).im| ≤ 1 / 2 := fun i => by
    rw [Complex.conj_im, abs_neg]; exact hΓim i
  have hΓb : ∀ i : S, ‖gammaOf (i : ℂ) - ((σ i / 2 : ℤ) : ℂ) * ((2 * h : ℝ) : ℂ)‖ ≤
      (C + 1) / 2 * h + h + 1 / 2 := fun i => by
    rw [hcast]
    refine (hnorm _ _).trans ?_
    rw [gammaOf_re]
    linarith [hhalf i, hΓim i]
  have hΓcb : ∀ i : S, ‖conj (gammaOf (i : ℂ)) - ((σ i / 2 : ℤ) : ℂ) * ((2 * h : ℝ) : ℂ)‖ ≤
      (C + 1) / 2 * h + h + 1 / 2 := fun i => by
    rw [hcast]
    refine (hnorm _ _).trans ?_
    rw [Complex.conj_re, gammaOf_re]
    linarith [hhalf i, hΓcim i]
  refine eq_of_multDiff_eq_zero fun z₀ => ?_
  by_contra hc
  set i₀ : S := ⟨z₀, hc⟩ with hi₀
  set PA : Set S := {i | σ i % 2 = 0 ∧ i ≠ i₀} with hPA
  set PB : Set S := {i | σ i % 2 = 1 ∧ i ≠ i₀} with hPB
  have hinj : ∀ P : Set S, (∀ i ∈ P, ∀ j ∈ P, σ i % 2 = σ j % 2) →
      Set.InjOn (fun i => σ i / 2) P := by
    intro P hP i hi j hj e
    apply hσ
    have := hP i hi j hj
    simp only at e
    omega
  have hne : ∀ i : S, i ≠ i₀ → gammaOf z₀ ≠ gammaOf (i : ℂ) := fun i hi e =>
    hi (Subtype.ext (gammaOf_injective e).symm)
  have hnec : ∀ i : S, i ≠ i₀ → conj (gammaOf z₀) ≠ conj (gammaOf (i : ℂ)) := fun i hi e =>
    hne i hi (by simpa using congrArg conj e)
  obtain ⟨f, hf, hfA, hf0⟩ := exists_window_blind_of_injOn_near_complex_lattice
    (fun i : S => gammaOf (i : ℂ)) (fun i => σ i / 2) PA
    (hinj PA fun i hi j hj => by rw [hi.1, hj.1]) (by positivity) hr (fun i _ => hΓb i)
    (fun i _ => hΓim i) (fun i hi => hne i hi.2)
  obtain ⟨g, hg, hgB, hg0⟩ := exists_window_blind_of_injOn_near_complex_lattice
    (fun i : S => conj (gammaOf (i : ℂ))) (fun i => σ i / 2) PB
    (hinj PB fun i hi j hj => by rw [hi.1, hj.1]) (by positivity) hr (fun i _ => hΓcb i)
    (fun i _ => hΓcim i) (fun i hi => hnec i hi.2)
  apply hc
  refine multDiff_eq_zero_of_pointImage_isolated hZ hZ' hW hf hg (fun z hz hcz => ?_) ?_
  · set i : S := ⟨z, hcz⟩
    have hne' : i ≠ i₀ := fun e => hz (congrArg Subtype.val e)
    rw [pointImage]
    rcases Int.emod_two_eq_zero_or_one (σ i) with he | ho
    · rw [show gammaOf z = gammaOf (i : ℂ) from rfl, hfA i ⟨he, hne'⟩, zero_mul]
    · rw [show conj (gammaOf z) = conj (gammaOf (i : ℂ)) from rfl, hgB i ⟨ho, hne'⟩, map_zero,
        mul_zero]
  · rw [pointImage]
    exact mul_ne_zero hf0 ((map_ne_zero _).mpr hg0)

/-! ### Resolution at every depth -/

theorem reflect_re_eq (z : ℂ) : (reflect z).re = 1 - z.re := by simp [reflect]

theorem reflect_im_eq (z : ℂ) : (reflect z).im = z.im := by simp [reflect]

/-- The site of a point: itself on or right of the line, its FE partner otherwise. -/
def siteOf (z : ℂ) : ℂ := if 1 / 2 ≤ z.re then z else reflect z

theorem siteOf_re (z : ℂ) : 1 / 2 ≤ (siteOf z).re := by
  unfold siteOf
  split_ifs with h
  · exact h
  · rw [reflect_re_eq]; linarith

theorem siteOf_im (z : ℂ) : (siteOf z).im = z.im := by
  unfold siteOf
  split_ifs
  · rfl
  · exact reflect_im_eq z

theorem siteOf_eq (z : ℂ) : siteOf z = z ∨ siteOf z = reflect z := by
  unfold siteOf
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Resolution at every depth.** Tempered configurations whose union has `g`-separated heights
apart from FE partners, with `g > π/a`, are determined by their Weil forms on `C²` tests
supported in `[−a, a]`, whatever the depths. -/
theorem eq_of_weil_eq_of_heightSeparated_of_lt {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {g a : ℝ} (ha : 0 < a) (hg : 0 < g) (hga : π / a < g)
    (hsep : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ →
      ρ' ≠ reflect ρ → g ≤ |ρ.im - ρ'.im|)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  classical
  have hU : ∀ z, multDiff Z Z' z ≠ 0 → siteOf z ∈ Z.carrier ∪ Z'.carrier := by
    intro z hz
    have hzU := mem_carrier_of_multDiff_ne_zero hz
    rcases siteOf_eq z with e | e
    · rw [e]; exact hzU
    · rw [e, Set.mem_union, reflect_mem_iff, reflect_mem_iff]; exact hzU
  refine eq_of_mimic_of_count_le hZ hZ' (D := 2 / g) (C := 2) (by positivity) ?_
    (fun f hf => hW f hf.1 hf.2) fun s x y hxy hs => ?_
  · rw [div_lt_iff₀ ha] at hga
    rw [show π * (2 / g) = 2 * π / g by ring, div_lt_iff₀ hg]
    linarith
  -- at most two points of the cluster per site
  have hfib : ∀ b ∈ s.image siteOf, (s.filter fun z => siteOf z = b).card ≤ 2 := by
    intro b _
    refine (Finset.card_le_card (t := {b, reflect b}) fun z hz => ?_).trans Finset.card_le_two
    rw [Finset.mem_filter] at hz
    rcases siteOf_eq z with e | e
    · rw [← hz.2, e]; simp
    · have : z = reflect b := by rw [← hz.2, e, Zeta23.reflect_reflect]
      simp [this]
  have h2 := Finset.card_le_mul_card_image s 2 hfib
  -- distinct sites are `g`-separated
  have hsites : ∀ u ∈ (s.image siteOf).image Complex.im, ∀ v ∈ (s.image siteOf).image Complex.im,
      u ≠ v → g ≤ |u - v| := by
    intro u hu v hv huv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hb'
    have hne : siteOf z' ≠ siteOf z := fun e => huv (by rw [e])
    have hnr : siteOf z' ≠ reflect (siteOf z) := by
      intro e
      have h1 := siteOf_re z'
      have h2 := siteOf_re z
      rw [e, reflect_re_eq] at h1
      have hre : (siteOf z).re = 1 / 2 := by linarith
      apply hne
      rw [e]
      apply Complex.ext
      · rw [reflect_re_eq, hre]; norm_num
      · rw [reflect_im_eq]
    exact hsep _ (hU z (hs z hz).1) _ (hU z' (hs z' hz').1) hne hnr
  have hinj : Set.InjOn Complex.im ((s.image siteOf : Finset ℂ) : Set ℂ) := by
    intro b hb b' hb' e
    by_contra hne
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hb'
    have := hsites _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hz)) _
      (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hz'))
    have hsep' := hsep _ (hU z (hs z hz).1) _ (hU z' (hs z' hz').1) (Ne.symm hne) (by
      intro e'
      have h1 := siteOf_re z'
      have h2 := siteOf_re z
      rw [e', reflect_re_eq] at h1
      have hre : (siteOf z).re = 1 / 2 := by linarith
      apply hne
      rw [e']
      apply Complex.ext
      · rw [reflect_re_eq, hre]; norm_num
      · rw [reflect_im_eq])
    rw [e, sub_self, abs_zero] at hsep'
    linarith
  have hcard := card_le_of_separated_of_subset_Icc hg hxy ((s.image siteOf).image Complex.im)
    hsites (fun u hu => by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
      rw [siteOf_im]
      exact (hs z hz).2)
  rw [Finset.card_image_of_injOn hinj] at hcard
  have h2' : (s.card : ℝ) ≤ 2 * ((s.image siteOf).card : ℝ) := by exact_mod_cast h2
  calc (s.card : ℝ) ≤ 2 * ((y - x) / g + 1) := h2'.trans (by linarith)
    _ = 2 / g * (y - x) + 2 := by field_simp

/-- **Hiding at every depth needs a near-collision below `π/a`.** Two tempered configurations
with different carriers and one image at aperture `a` contain, for every `g > π/a`, two points of
different FE orbits at height distance `< g`. -/
theorem exists_near_pair_of_mimic_of_lt {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') (hne : Z.carrier ≠ Z'.carrier) {g a : ℝ} (ha : 0 < a) (hg : 0 < g)
    (hga : π / a < g)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) :
    ∃ ρ ∈ Z.carrier ∪ Z'.carrier, ∃ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ ∧ ρ' ≠ reflect ρ ∧
      |ρ.im - ρ'.im| < g := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  exact hne (eq_of_weil_eq_of_heightSeparated_of_lt hZ hZ' ha hg hga
    (fun ρ hρ ρ' hρ' h1 h2 => h ρ hρ ρ' hρ' h1 h2) hW).1

end GaloisForLFunctions.ZeroConfigurationGeometry
