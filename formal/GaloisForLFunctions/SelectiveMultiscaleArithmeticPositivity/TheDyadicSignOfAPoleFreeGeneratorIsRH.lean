import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OnePrimeSeesTheWholeDefectOfZeta
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheDyadicSignIsRigid

/-!
# The dyadic sign of a pole-free generator is RH, at every overlap

The pole moments of a test are its transforms at `±i/2`, the spectral points `γ_1 = −i/2` and
`γ_0 = i/2` of the pole `s = 1` and its reflection. A generator with both moments zero has its
whole `T_{log p}`-tower inside the pole complement: `A(Σ c_k T_{k log p} g) = A(g) Σ c_k p^{−k/2}`.

The annihilating tests of `OnePrimeSeesTheWholeDefectOfZeta` kill a sparse set of points right of
the line. Adding the pole `τ = 1` to that set (`exists_test_killing_deep_zeros_poleFree_small`)
gives pole-free generators supported in `[−ε, ε]` that see any finite set of outer Frobenius
eigenvalues `p^{ρ−½}`:

* **Index law** (`zeta_poleFree_small_tower_law`): for every prime `p` and every `ε > 0`, some
  window of the tower of some pole-free `C²` generator supported in `[−ε, ε]` carries `n` negative
  squares of Weil's form iff `ζ` has at least `n` distinct outer eigenvalues `p^{ρ−½}`.
* **The sign is RH** (`riemannHypothesis_iff_towerPositive_poleFree_small`,
  `riemannHypothesis_iff_dyadicPositive_poleFree_small`): RH holds iff `Λ` is positive along the
  `p`-tower of every pole-free `C²` generator supported in `[−ε, ε]`, for one (every) prime `p` and
  one (every) `ε > 0`.
* **Under RH the twins fail** (`not_towerPositive_liouvilleTwin_of_riemannHypothesis`,
  `not_towerPositive_perturbed_of_riemannHypothesis`): with `TheDyadicSignIsRigid`, the Liouville
  twin and every `n^{−η}` perturbation of `Λ` fail on the tower of every nonnegative generator.

So selective Toeplitz positivity on the pole complement with one generator and one prime has no
intermediate content at any overlap: the support length of the generator, measured against
`log 2`, can be taken as small as wished.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open Zeta23 GaloisForLFunctions.HTGeometry ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

local notation "Tr" => ArithmeticCastelnuovoSeveri.translate

theorem gammaOf_one : gammaOf 1 = -(I / 2) := by
  rw [gammaOf, div_eq_iff I_ne_zero]
  ring_nf
  rw [I_sq]
  ring

theorem reflect_one : reflect 1 = 0 := by simp [reflect]

theorem gammaOf_zero : gammaOf 0 = I / 2 := by
  rw [gammaOf, div_eq_iff I_ne_zero]
  ring_nf
  rw [I_sq]
  ring

/-- `1` is not a nontrivial zero of `ζ`. -/
theorem one_not_mem_zetaZeroConfig : (1 : ℂ) ∉ zetaZeroConfig.carrier := by
  intro h
  have hm : Zeta23.IsNontrivialZero (1 : ℂ) := h
  exact absurd hm.2.2 (by norm_num)

/-- **A pole-free test killing the deep zeros.** For a deep-sparse configuration not containing
`1`, a set `F` of right zeros, a depth `σ₀ > ½` and `ε > 0`, a `C²` test supported in `[−ε, ε]`
has both pole moments zero, vanishes at `γ_τ, γ_{1−τ̄}` for every right zero `τ ∉ F` of depth
`≥ σ₀`, and at neither point for `τ ∈ F`. -/
theorem exists_test_killing_deep_zeros_poleFree_small (Z : ZeroConfig) (hsp : DeepSparse Z)
    (h1 : (1 : ℂ) ∉ Z.carrier) {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) (F : Set ℂ)
    (hF : ∀ τ ∈ F, τ ∈ rightZeros Z) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ tsupport g ⊆ Set.Icc (-ε) ε ∧
      paperFT g (I / 2) = 0 ∧ paperFT g (-(I / 2)) = 0 ∧
      (∀ τ ∈ rightZeros Z, σ₀ ≤ τ.re → τ ∉ F →
        paperFT g (gammaOf τ) = 0 ∧ paperFT g (gammaOf (reflect τ)) = 0) ∧
      ∀ τ ∈ F, paperFT g (gammaOf τ) ≠ 0 ∧ paperFT g (gammaOf (reflect τ)) ≠ 0 := by
  obtain ⟨s, hs0, hs1, hsum⟩ := hsp σ₀ hσ₀
  set S : Set ℂ := {τ : ℂ | τ ∈ rightZeros Z ∧ σ₀ ≤ τ.re} with hS
  set A₀ : Set ℂ := S \ F with hA₀
  set A : Set ℂ := A₀ ∪ {1} with hA
  have hA₀S : A₀ ⊆ S := Set.sdiff_subset
  have hA₀r : ∀ τ ∈ A₀, τ ∈ rightZeros Z := fun τ hτ => (hA₀S hτ).1
  have h1A₀ : (1 : ℂ) ∉ A₀ := fun h => h1 (hA₀r 1 h).1
  have hAre : ∀ τ ∈ A, 1 / 2 < τ.re := by
    rintro τ (hτ | rfl)
    · exact (hA₀r τ hτ).2
    · norm_num
  have hAc : A.Countable :=
    ((SquareRootThreshold.countable_carrier Z).mono fun τ hτ => (hA₀r τ hτ).1).union
      (Set.countable_singleton 1)
  set w : ℂ → ℝ := fun τ => ‖gammaOf τ‖⁻¹ ^ s
  have hsum₀ : Summable fun τ : A₀ => w τ := by
    simpa only [Function.comp_def, Set.coe_inclusion] using
      hsum.comp_injective (Set.inclusion_injective hA₀S)
  have hsumA : Summable fun τ : A => ‖gammaOf (τ : ℂ)‖⁻¹ ^ s := by
    have hi₀ := (summable_subtype_iff_indicator (f := w)).mp hsum₀
    have hi₁ : Summable (({1} : Set ℂ).indicator w) :=
      summable_of_ne_finset_zero (s := {1}) fun τ hτ => by
        rw [Finset.mem_singleton] at hτ
        exact Set.indicator_of_notMem (by simpa using hτ) _
    have hdisj : Disjoint A₀ ({1} : Set ℂ) := Set.disjoint_singleton_right.mpr h1A₀
    refine (summable_subtype_iff_indicator (f := w)).mpr ?_
    rw [hA, Set.indicator_union_of_disjoint hdisj]
    exact hi₀.add hi₁
  obtain ⟨g, hg, hgc, hz, hnz⟩ := exists_test_killing_small A hAre hAc hs0 hs1 hsumA hε
  have hmemA : ∀ τ ∈ rightZeros Z, σ₀ ≤ τ.re → τ ∉ F → τ ∈ A := fun τ hτ hle hτF =>
    Or.inl ⟨⟨hτ, hle⟩, hτF⟩
  have hpole := hz 1 (Or.inr rfl)
  rw [gammaOf_one, reflect_one, gammaOf_zero] at hpole
  refine ⟨g, hg, hgc, hpole.2, hpole.1, fun τ hτ hle hτF => hz τ (hmemA τ hτ hle hτF),
    fun τ₀ hτ₀ => ?_⟩
  have hτ₀r := hF τ₀ hτ₀
  have hre := hτ₀r.2
  have hne1 : τ₀ ≠ 1 := fun h => h1 (h ▸ hτ₀r.1)
  -- the points of `A` never meet `γ_{τ₀}` or `γ_{1−τ̄₀}`
  have hsep : ∀ τ ∈ A, τ ≠ τ₀ ∧ τ ≠ reflect τ₀ ∧ reflect τ ≠ τ₀ ∧ reflect τ ≠ reflect τ₀ := by
    rintro τ (hτ | rfl)
    · have hτr := hA₀r τ hτ
      have hτF : τ ∉ F := hτ.2
      refine ⟨fun h => hτF (h ▸ hτ₀), fun h => ?_, fun h => ?_, fun h => hτF ?_⟩
      · have := congrArg Complex.re h
        rw [re_reflect] at this; linarith [hτr.2]
      · have := congrArg Complex.re h
        rw [re_reflect] at this; linarith [hτr.2]
      · rw [← Zeta23.reflect_reflect τ, h, Zeta23.reflect_reflect]; exact hτ₀
    · refine ⟨hne1.symm, fun h => ?_, fun h => ?_, fun h => hne1 ?_⟩
      · have := congrArg Complex.re h
        rw [re_reflect, Complex.one_re] at this; linarith
      · rw [reflect_one] at h
        have := congrArg Complex.re h
        rw [Complex.zero_re] at this; linarith
      · rw [← Zeta23.reflect_reflect τ₀, ← h, Zeta23.reflect_reflect]
  constructor
  · refine hnz _
      (by rw [SquareRootThreshold.im_gammaOf]; exact (by linarith : 1 / 2 - τ₀.re < 0).ne)
      fun τ hτ => ⟨fun h => (hsep τ hτ).1 (gammaOf_injective h).symm,
        fun h => (hsep τ hτ).2.2.1 (gammaOf_injective h).symm⟩
  · refine hnz _ (by
        rw [SquareRootThreshold.im_gammaOf, re_reflect]
        exact (by linarith : 0 < 1 / 2 - (1 - τ₀.re)).ne')
      fun τ hτ => ⟨fun h => (hsep τ hτ).2.1 (gammaOf_injective h).symm,
        fun h => (hsep τ hτ).2.2.2 (gammaOf_injective h).symm⟩

/-- **Pole-free small generators see every finite set of outer eigenvalues.** -/
theorem exists_poleFree_small_test_card_le_towerDefect (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) (h1 : (1 : ℂ) ∉ Z.carrier) {ℓ : ℝ} (hℓ : 0 < ℓ) {ε : ℝ} (hε : 0 < ε)
    (O : Finset ℂ) (hO : ∀ b ∈ O, b ∈ outerEig Z ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ tsupport g ⊆ Set.Icc (-ε) ε ∧
      paperFT g (I / 2) = 0 ∧ paperFT g (-(I / 2)) = 0 ∧
      ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g ℓ K) := by
  rcases O.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨g, hg, hgs, hp1, hp2, -, -⟩ := exists_test_killing_deep_zeros_poleFree_small Z hsp h1
      (σ₀ := 1) (by norm_num) ∅ (fun _ h => h.elim) hε
    exact ⟨g, hg, hgs, hp1, hp2, ∅, by simp⟩
  have hO' : ∀ b ∈ O, ∃ ρ, ρ ∈ rightZeros Z ∧ frobEig ℓ ρ = b := fun b hb => hO b hb
  choose! r hr hrb using hO'
  set F : Finset ℂ := O.image r
  set σ₀ : ℝ := O.inf' hne fun b => (r b).re
  have hσ₀le : ∀ b ∈ O, σ₀ ≤ (r b).re := fun b hb => Finset.inf'_le _ hb
  have hσ₀ : 1 / 2 < σ₀ := by
    obtain ⟨b, hb, hbe⟩ := Finset.exists_mem_eq_inf' hne fun b => (r b).re
    rw [show σ₀ = (r b).re from hbe]
    exact (hr b hb).2
  have hFr : ∀ τ ∈ F, τ ∈ rightZeros Z := fun τ hτ => by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hτ
    exact hr b hb
  obtain ⟨g, hg, hgs, hp1, hp2, hkill, hkeep⟩ :=
    exists_test_killing_deep_zeros_poleFree_small Z hsp h1 hσ₀ ↑F hFr hε
  have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
  have hrF : ∀ b ∈ O, r b ∈ F := fun b hb => Finset.mem_image_of_mem r hb
  refine ⟨g, hg, hgs, hp1, hp2, card_le_towerDefect_of_activeWellFounded Z hZ hg hgc hℓ O
    (fun b hb => ⟨⟨r b, hr b hb, hrb b hb⟩, ?_⟩)
    fun b hb => ⟨r b, hr b hb, hrb b hb, activeLevels_wellFounded_of_kill Z hkill (hσ₀le b hb)⟩⟩
  refine frobWeight_ne_zero_of_single Z (hr b hb) (hrb b hb) (hkeep _ (hrF b hb))
    fun τ hτ hne he => ?_
  have hre : τ.re = (r b).re := re_eq_of_norm_frobEig_eq hℓ (by rw [he, hrb b hb])
  have hτr : τ ∈ rightZeros Z := ⟨hτ, by rw [hre]; exact (hr b hb).2⟩
  refine (hkill τ hτr (by rw [hre]; exact hσ₀le b hb) fun hm => hne ?_).1
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hm
  have : b' = b := by rw [← hrb b' hb', he]
  rw [this]

/-- The pole-free small-support index law for deep-sparse configurations. -/
theorem deepSparse_poleFree_small_tower_law (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) (h1 : (1 : ℂ) ∉ Z.carrier) {ℓ : ℝ} (hℓ : 0 < ℓ) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) :
    (∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ tsupport g ⊆ Set.Icc (-ε) ε ∧
      paperFT g (I / 2) = 0 ∧ paperFT g (-(I / 2)) = 0 ∧
      ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
      (n : ℕ∞) ≤ (outerEig Z ℓ).encard := by
  constructor
  · rintro ⟨g, hg, hgs, -, -, K, hK⟩
    have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    exact (deepSparse_tower_law Z hZ hsp hℓ n).mp ⟨g, hg, hgc, K, hK⟩
  · intro hn
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hn
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htc
    obtain ⟨g, hg, hgs, hp1, hp2, K, hK⟩ := exists_poleFree_small_test_card_le_towerDefect Z hZ
      hsp h1 hℓ hε htfin.toFinset fun b hb => hts (htfin.mem_toFinset.mp hb)
    have hcard : htfin.toFinset.card = n := by
      have := htfin.encard_eq_coe_toFinset_card
      rw [htc] at this
      exact_mod_cast this.symm
    exact ⟨g, hg, hgs, hp1, hp2, K, hcard ▸ hK⟩

/-- **The pole-free one-prime index law for `ζ`.** For every prime `p` and every `ε > 0`, some
window of the `p`-tower of some pole-free `C²` generator supported in `[−ε, ε]` carries `n`
negative squares of Weil's form iff `ζ` has at least `n` distinct outer eigenvalues `p^{ρ−½}`. -/
theorem zeta_poleFree_small_tower_law {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ tsupport g ⊆ Set.Icc (-ε) ε ∧
      paperFT g (I / 2) = 0 ∧ paperFT g (-(I / 2)) = 0 ∧
      ∃ K : Finset ℤ, n ≤ hermNegIndex (weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        fun k : K => Tr (((k : ℤ) : ℝ) * Real.log p) g)) ↔
      (n : ℕ∞) ≤ (outerEig zetaZeroConfig (Real.log p)).encard := by
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [← deepSparse_poleFree_small_tower_law _ temperedConfig_zetaZeroConfig deepSparse_zeta
    one_not_mem_zetaZeroConfig hℓ hε n]
  refine exists_congr fun g => ⟨fun ⟨hg, hgs, hp1, hp2, K, hK⟩ => ⟨hg, hgs, hp1, hp2, K, ?_⟩,
    fun ⟨hg, hgs, hp1, hp2, K, hK⟩ => ⟨hg, hgs, hp1, hp2, K, ?_⟩⟩
  all_goals
    have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    have hw : weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        (fun k : K => Tr (((k : ℤ) : ℝ) * Real.log p) g) =
        towerGram zetaZeroConfig g (Real.log p) K :=
      weilGram_eq_zeroGram _ (fun _ => translate_contDiff hg _)
        (fun _ => translate_hasCompactSupport hgc _)
  · rwa [← hw]
  · rwa [hw]

/-- **The tower sign on the pole complement is RH at every prime and every overlap.** For every
prime `p` and every `ε > 0`, RH holds iff `Λ` is positive along the `p`-tower of every pole-free `C²`
generator supported in `[−ε, ε]`. -/
theorem riemannHypothesis_iff_towerPositive_poleFree_small {p : ℕ} (hp : p.Prime) {ε : ℝ}
    (hε : 0 < ε) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Set.Icc (-ε) ε →
      paperFT g (I / 2) = 0 → paperFT g (-(I / 2)) = 0 →
        TowerPositive (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g (Real.log p) := by
  have hlaw := zeta_poleFree_small_tower_law hp hε 1
  constructor
  · intro hRH g hg hgs _ _ K
    have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    exact (riemannHypothesis_iff_onePrime_towers hp).mp hRH g hg hgc K
  · intro hpos
    rw [← rightZeros_zeta_eq_empty_iff]
    by_contra hne
    obtain ⟨ρ, hρ⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hne' : (outerEig zetaZeroConfig (Real.log p)).Nonempty :=
      ⟨frobEig (Real.log p) ρ, ρ, hρ, rfl⟩
    have h1 : ((1 : ℕ) : ℕ∞) ≤ (outerEig zetaZeroConfig (Real.log p)).encard := by
      rw [Nat.cast_one]; exact Set.one_le_encard_iff_nonempty.mpr hne'
    obtain ⟨g, hg, hgs, hp1, hp2, K, hK⟩ := hlaw.mpr h1
    have h0 := hpos g hg hgs hp1 hp2 K
    omega

/-- **The dyadic sign on the pole complement is RH at every overlap.** -/
theorem riemannHypothesis_iff_dyadicPositive_poleFree_small {ε : ℝ} (hε : 0 < ε) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Set.Icc (-ε) ε →
      paperFT g (I / 2) = 0 → paperFT g (-(I / 2)) = 0 →
        DyadicPositive (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g := by
  simpa using riemannHypothesis_iff_towerPositive_poleFree_small Nat.prime_two hε

/-! ### Under RH the twins fail on every tower -/

/-- Under RH `Λ` is positive along the tower of every `C²` compactly supported generator. -/
theorem towerPositive_vonMangoldt_of_riemannHypothesis (hRH : RiemannHypothesis) {p : ℕ}
    (hp : p.Prime) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    TowerPositive (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) g (Real.log p) :=
  (riemannHypothesis_iff_onePrime_towers hp).mp hRH g hg hgc

/-- **Under RH the Liouville twin fails on every Hecke tower** of every nonnegative nonzero `C²`
generator, although it dominates `ζ` on each nonnegative test
(`ArithmeticCorrespondencePositivity.weilPositive_nonneg_transfers`). -/
theorem not_towerPositive_liouvilleTwin_of_riemannHypothesis (hRH : RiemannHypothesis) {p : ℕ}
    (hp : p.Prime) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 (cx f)) (hfc : HasCompactSupport (cx f))
    (hf0 : ∀ x, 0 ≤ f x) (hne : ∃ x, f x ≠ 0) :
    ¬ TowerPositive ArithmeticCorrespondencePositivity.liouvilleTwin (cx f) (Real.log p) :=
  fun h => not_towerPositive_liouvilleTwin_and_vonMangoldt hf hfc hf0 hne
    (Real.log_pos (by exact_mod_cast hp.one_lt))
    ⟨h, towerPositive_vonMangoldt_of_riemannHypothesis hRH hp hf hfc⟩

/-- **Under RH no `n^{−η}` perturbation of `Λ` is tower positive** along a nonnegative generator,
`0 < η < 1/2`, at any prime. -/
theorem not_towerPositive_perturbed_of_riemannHypothesis (hRH : RiemannHypothesis) {p : ℕ}
    (hp : p.Prime) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 (cx f)) (hfc : HasCompactSupport (cx f))
    (hf0 : ∀ x, 0 ≤ f x) (hne : ∃ x, f x ≠ 0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hη2 : η < 1 / 2) :
    ¬ TowerPositive (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + ε * (n : ℝ) ^ (-η)) (cx f)
      (Real.log p) :=
  fun h => not_towerPositive_and_perturbed _ hf hfc hf0 hne hε hη hη2
    (Real.log_pos (by exact_mod_cast hp.one_lt))
    ⟨towerPositive_vonMangoldt_of_riemannHypothesis hRH hp hf hfc, h⟩

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
