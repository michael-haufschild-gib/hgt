import GaloisForLFunctions.ZeroConfigurationGeometry.IsolationIdentifiesTheCluster
import GaloisForLFunctions.ZeroConfigurationGeometry.BlindWindowsAtTheUniformDensity

/-!
# Sparse on-line clusters never cancel

Two mimics at aperture `a` have the same image on every pair `(f, g)` of windows of aperture `a`,
and a point of the cluster contributes `c(z) f̂(γ_z) conj ĝ(conj γ_z)`. To read one point of an
on-line cluster it suffices that `f` is blind to one half of the rest and `g` to the other half:
the camera of lag aperture `2a` is split between its two windows.

* **Pair isolation** (`multDiff_eq_zero_of_pointImage_isolated`). If the pair image of `(f, g)`
  vanishes at every other point of the cluster and not at `z₀`, then `c(z₀) = 0`.
* **Blind windows from a matching** (`exists_window_blind_of_injOn_near_lattice`). Points matched
  injectively into a lattice `Hℤ` at bounded distance are blinded at every aperture `> π/H`.
* **The density criterion** (`eq_of_mimic_of_onLine_count_le`). Match the heights of the cluster
  into `D⁻¹ℤ` (Hall), and split by the parity of the lattice index. Each half lies at bounded
  distance from `2D⁻¹ℤ`, so windows of aperture `a > πD/2` blind each half. Hence mimics at
  aperture `a` whose cluster lies on the critical line with upper uniform density `< 2a/π` are
  equal. No separation of the cluster is needed.

The criterion is sharp: the on-line lattice pair of `lattice_resolution_sharp` has the cluster
`(π/(2a))ℤ`, of density exactly `2a/π`, and cancels at aperture `a`.
-/

open MeasureTheory Complex Set Filter
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- **Pair isolation.** -/
theorem multDiff_eq_zero_of_pointImage_isolated {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {a : ℝ} (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    {z₀ : ℂ} {f g : ℝ → ℂ} (hf : ApertureWindow a f) (hg : ApertureWindow a g)
    (hblind : ∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → pointImage f g z = 0)
    (hsee : pointImage f g z₀ ≠ 0) : multDiff Z Z' z₀ = 0 := by
  have h := W_sub_W_eq_tsum hZ hZ' hf.1 hf.hasCompactSupport hg.1 hg.hasCompactSupport
  rw [W_eq_of_mimic hZ hZ' hW hf hg, sub_self, tsum_eq_single z₀ fun z hz => ?_] at h
  · exact (mul_eq_zero.mp h.symm).resolve_right hsee
  · by_cases hc : multDiff Z Z' z = 0
    · rw [hc, zero_mul]
    · rw [hblind z hz hc, mul_zero]

/-- **Blind windows from a matching into a lattice.** If the points `λ_i`, `i ∈ P`, are matched
injectively to lattice points `τ_i H` at distance `≤ L`, every aperture `> π/H` has a window blind
to them that sees any given `z₀` off them. -/
theorem exists_window_blind_of_injOn_near_lattice {ι : Type*} (lam : ι → ℝ) (τ : ι → ℤ)
    (P : Set ι) (hτ : Set.InjOn τ P) {H L r : ℝ} (hH : 0 < H) (hr : π / H < r)
    (hL : ∀ i ∈ P, |lam i - τ i * H| ≤ L) {z₀ : ℂ} (hz₀ : ∀ i ∈ P, z₀ ≠ lam i) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ i ∈ P, paperFT f (lam i) = 0) ∧ paperFT f z₀ ≠ 0 := by
  classical
  obtain ⟨c, ⟨hc0, hcH⟩, hcE⟩ := SquareRootThreshold.exists_mem_Ioo_notMem_of_countable hH
    (Set.countable_range fun k : ℤ => z₀.re - k * H)
  set ν : ℤ → ℝ := fun k => if hk : ∃ i ∈ P, τ i = k then lam hk.choose else k * H + c with hν
  have hνin : ∀ k (hk : ∃ i ∈ P, τ i = k), ν k = lam hk.choose := fun k hk => by
    simp only [hν, dif_pos hk]
  have hνout : ∀ k, (¬ ∃ i ∈ P, τ i = k) → ν k = k * H + c := fun k hk => by
    simp only [hν, dif_neg hk]
  have hντ : ∀ i ∈ P, ν (τ i) = lam i := fun i hi => by
    have hk : ∃ j ∈ P, τ j = τ i := ⟨i, hi, rfl⟩
    rw [hνin _ hk, hτ hk.choose_spec.1 hi hk.choose_spec.2]
  have hL0 : 0 ≤ L ∨ P = ∅ := by
    by_cases hP : P = ∅
    · exact Or.inr hP
    · obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hP
      exact Or.inl ((abs_nonneg _).trans (hL i hi))
  have hνb : ∀ k : ℤ, |ν k - k * H| ≤ |L| + H := by
    intro k
    by_cases hk : ∃ i ∈ P, τ i = k
    · obtain ⟨j, hjP, hjl, hj⟩ : ∃ j ∈ P, lam hk.choose = lam j ∧ τ j = k :=
        ⟨_, hk.choose_spec.1, rfl, hk.choose_spec.2⟩
      rw [hνin k hk, hjl, ← hj]
      exact (hL j hjP).trans (by linarith [le_abs_self L])
    · rw [hνout k hk, add_sub_cancel_left, abs_of_pos hc0]
      linarith [abs_nonneg L]
  have hz₀' : ∀ k, z₀ ≠ ν k := by
    intro k hk0
    by_cases hk : ∃ i ∈ P, τ i = k
    · exact hz₀ hk.choose hk.choose_spec.1 (by rw [hk0, hνin k hk])
    · apply hcE
      refine ⟨k, ?_⟩
      have := congrArg Complex.re hk0
      rw [Complex.ofReal_re, hνout k hk] at this
      show z₀.re - k * H = c
      linarith
  obtain ⟨f, hf, hfν, hf0⟩ := exists_window_blind_to_perturbed_lattice hH hr ν hνb hz₀'
  exact ⟨f, hf, fun i hi => by rw [← hντ i hi]; exact hfν (τ i), hf0⟩

theorem gammaOf_of_re_eq_half {z : ℂ} (hz : z.re = 1 / 2) : gammaOf z = (z.im : ℂ) := by
  have e : z - 1 / 2 = I * (z.im : ℂ) := by
    apply Complex.ext <;> simp [hz]
  rw [gammaOf, e, mul_div_cancel_left₀ _ Complex.I_ne_zero]

/-- **Sparse on-line clusters never cancel.** Mimics at aperture `a` whose cluster lies on the
critical line, with at most `D(y − x) + C` points at heights in every `[x, y]` and `πD < 2a`, are
equal. -/
theorem eq_of_mimic_of_onLine_count_le {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {a D C : ℝ} (hD : 0 < D) (hDa : π * D < 2 * a)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    (hline : ∀ z, multDiff Z Z' z ≠ 0 → z.re = 1 / 2)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ z.im ∈ Icc x y) → (s.card : ℝ) ≤ D * (y - x) + C) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  classical
  set S : Set ℂ := {z | multDiff Z Z' z ≠ 0} with hS
  set lam : S → ℝ := fun z => (z : ℂ).im with hlam
  -- the rescaled heights have count bound `(1, C)`
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
  -- the lattice index of a matched point, halved
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
  refine eq_of_multDiff_eq_zero fun z₀ => ?_
  by_contra hc
  set i₀ : S := ⟨z₀, hc⟩ with hi₀
  -- the two halves of the rest of the cluster
  set PA : Set S := {i | σ i % 2 = 0 ∧ i ≠ i₀} with hPA
  set PB : Set S := {i | σ i % 2 = 1 ∧ i ≠ i₀} with hPB
  have hinj : ∀ P : Set S, (∀ i ∈ P, ∀ j ∈ P, σ i % 2 = σ j % 2) → Set.InjOn (fun i => σ i / 2) P := by
    intro P hP i hi j hj e
    apply hσ
    have := hP i hi j hj
    simp only at e
    omega
  have hoff : ∀ i : S, i ≠ i₀ → (z₀.im : ℂ) ≠ (lam i : ℂ) := by
    intro i hne e
    apply hne
    apply Subtype.ext
    have him : z₀.im = (i : ℂ).im := Complex.ofReal_injective e
    apply Complex.ext
    · rw [hline z₀ hc, hline i i.2]
    · exact him.symm
  obtain ⟨f, hf, hfA, hf0⟩ := exists_window_blind_of_injOn_near_lattice lam (fun i => σ i / 2) PA
    (hinj PA fun i hi j hj => by rw [hi.1, hj.1]) (by positivity) hr
    (fun i _ => hhalf i) (fun i hi => hoff i hi.2)
  obtain ⟨g, hg, hgB, hg0⟩ := exists_window_blind_of_injOn_near_lattice lam (fun i => σ i / 2) PB
    (hinj PB fun i hi j hj => by rw [hi.1, hj.1]) (by positivity) hr
    (fun i _ => hhalf i) (fun i hi => hoff i hi.2)
  apply hc
  refine multDiff_eq_zero_of_pointImage_isolated hZ hZ' hW hf hg (fun z hz hcz => ?_) ?_
  · set i : S := ⟨z, hcz⟩
    have hne : i ≠ i₀ := fun e => hz (congrArg Subtype.val e)
    rw [pointImage, gammaOf_of_re_eq_half (hline z hcz)]
    rcases Int.emod_two_eq_zero_or_one (σ i) with he | ho
    · rw [show (z.im : ℂ) = ((lam i : ℝ) : ℂ) from rfl, hfA i ⟨he, hne⟩, zero_mul]
    · rw [Complex.conj_ofReal, show (z.im : ℂ) = ((lam i : ℝ) : ℂ) from rfl, hgB i ⟨ho, hne⟩,
        map_zero, mul_zero]
  · rw [pointImage, gammaOf_of_re_eq_half (hline z₀ hc), Complex.conj_ofReal]
    exact mul_ne_zero hf0 ((map_ne_zero _).mpr hg0)

/-- **Separated on-line clusters.** Mimics at aperture `a` whose cluster lies on the critical line
with heights `δ`-separated, `δ > π/(2a)`, are equal. -/
theorem eq_of_mimic_of_onLine_separated {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδa : π / (2 * a) < δ)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    (hline : ∀ z, multDiff Z Z' z ≠ 0 → z.re = 1 / 2)
    (hsep : ∀ z z', multDiff Z Z' z ≠ 0 → multDiff Z Z' z' ≠ 0 → z ≠ z' → δ ≤ |z.im - z'.im|) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  refine eq_of_mimic_of_onLine_count_le hZ hZ' (D := δ⁻¹) (C := 1) (inv_pos.mpr hδ) ?_ hW hline
    fun s x y hxy hs => ?_
  · rw [div_lt_iff₀ (by positivity)] at hδa
    rw [← div_eq_mul_inv, div_lt_iff₀ hδ]
    linarith
  · have hinj : Set.InjOn Complex.im (s : Set ℂ) := by
      intro z hz z' hz' e
      by_contra hne
      have := hsep z z' (hs z hz).1 (hs z' hz').1 hne
      rw [e, sub_self, abs_zero] at this
      linarith
    have h := card_le_of_separated_of_subset_Icc hδ hxy (s.image Complex.im)
      (fun u hu v hv huv => by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hv
        exact hsep z z' (hs z hz).1 (hs z' hz').1 fun e => huv (by rw [e]))
      (fun u hu => by obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu; exact (hs z hz).2)
    rw [Finset.card_image_of_injOn hinj] at h
    calc (s.card : ℝ) ≤ (y - x) / δ + 1 := h
      _ = δ⁻¹ * (y - x) + 1 := by rw [div_eq_inv_mul]

end GaloisForLFunctions.ZeroConfigurationGeometry
