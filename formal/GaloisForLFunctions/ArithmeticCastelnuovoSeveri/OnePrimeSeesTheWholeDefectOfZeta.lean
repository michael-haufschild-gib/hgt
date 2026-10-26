import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AnnihilatingTestsForSparseSpectra
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OnePrimeAgainstTwoAndWolffTowerObstruction
import GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley
import GaloisForLFunctions.RHTower.XiZeroShortWeightDyadic
import GaloisForLFunctions.SquareRootThreshold.ZetaLagPositivityForcesCloseCompanions
import GaloisForLFunctions.RHTower.EvenLandauPairTest

/-!
# One prime sees the whole defect of `ζ`

A single prime tower `g(· − k log p)` sees an outer Frobenius eigenvalue `b = p^{ρ − ½}` once the
levels above `Re ρ` *at which the test is nonzero* contain no strictly increasing sequence: the
top-down class extraction of `OnePrimeSeesEveryWellFoundedLevel` only reads atoms of nonzero
weight (`activeLevels`, `card_le_towerDefect_of_activeWellFounded`).

Vertical accumulation of right zeros (the Wolff mechanism of
`OnePrimeAgainstTwoAndWolffTowerObstruction`) can therefore be removed by the test itself. If the
right zeros of depth `≥ σ` have convergence exponent below one for every `σ > ½`
(`DeepSparse`), the Ingham–Paley–Wiener annihilator of `AnnihilatingTestsForSparseSpectra`
kills all deep zeros except finitely many chosen representatives, at both points `γ_τ` and
`γ_{1−τ̄}`, and vanishes nowhere else off the real line. Every finite set of outer eigenvalues is
then seen by one window of one tower (`exists_test_card_le_towerDefect`), with no visibility,
well-foundedness or separation hypothesis:

  `sup_{g, K} neg(tower of g at scale ℓ on K) = #{distinct outer eigenvalues e^{ℓ(ρ−½)}}`
  (`deepSparse_tower_law`).

`ζ` is deep-sparse by the Ingham–Huxley zero-density estimate, summed over dyadic height boxes
(`deepSparse_zeta`). Hence at **every** prime `p` the `p`-tower of `ζ` carries one negative square
for each distinct `p^{ρ−½}` (`zeta_one_prime_tower_law`), and RH is equivalent to positivity of
the Weil form on all `p`-towers for one fixed prime (`riemannHypothesis_iff_onePrime_towers`).
At all but finitely many primes the eigenvalues are distinct and one tower carries the whole Hodge
defect, finite or infinite (`zeta_almost_every_prime_tower_law`).
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate Classical lp
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold
  (TemperedConfig temperedConfig_zetaZeroConfig carrierCopy carrierCopy_val)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Annihilating tests for countable families -/

/-- **Annihilating tests for sparse countable families.** If `a i ≠ 0` and `Σ_i |a_i|^{-s} < ∞`
for some `0 < s < 1`, a `C²` compactly supported test has transform vanishing at every `a i` and
at no other non-real point. The family is padded by the real points `2^{n+1}` and enumerated. -/
theorem exists_annihilating_test_of_countable {ι : Type*} [Countable ι] {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) {a : ι → ℂ} (ha : ∀ i, a i ≠ 0) (hsum : Summable fun i => ‖a i‖⁻¹ ^ s) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ i, paperFT g (a i) = 0) ∧
      ∀ w : ℂ, w.im ≠ 0 → (∀ i, w ≠ a i) → paperFT g w ≠ 0 := by
  set c : ℕ → ℂ := fun n => (((2 : ℝ) ^ (n + 1) : ℝ) : ℂ)
  set a' : ι ⊕ ℕ → ℂ := Sum.elim a c
  have ha' : ∀ j, a' j ≠ 0 := by
    rintro (i | n)
    · exact ha i
    · exact Complex.ofReal_ne_zero.mpr (by positivity)
  -- the padding is geometric
  set r : ℝ := (2 : ℝ)⁻¹ ^ s
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hs0
  have hc : ∀ n : ℕ, ‖c n‖⁻¹ ^ s = r * r ^ n := by
    intro n
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), ← inv_pow, ← pow_succ',
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  have hcs : Summable fun n => ‖c n‖⁻¹ ^ s := by
    simp_rw [hc]; exact (summable_geometric_of_lt_one hr0 hr1).mul_left r
  have hsum' : Summable fun j => ‖a' j‖⁻¹ ^ s := Summable.sum _ hsum hcs
  obtain ⟨hden⟩ := nonempty_denumerable (ι ⊕ ℕ)
  set e : ι ⊕ ℕ ≃ ℕ := Denumerable.eqv (ι ⊕ ℕ)
  have hb := (e.symm.summable_iff (f := fun j => ‖a' j‖⁻¹ ^ s)).mpr hsum'
  obtain ⟨g, hg, hgc, hz, hnz⟩ := exists_annihilating_test hs0 hs1 (a := fun k => a' (e.symm k))
    (fun k => ha' _) hb
  refine ⟨g, hg, hgc, fun i => ?_, fun w hw hwa => hnz w hw fun k => ?_⟩
  · simpa [a'] using hz (e (Sum.inl i))
  · show w ≠ a' (e.symm k)
    generalize e.symm k = j
    rcases j with i | n
    · exact hwa i
    · rintro rfl
      exact hw (Complex.ofReal_im _)

/-! ### 2. Extraction on the support of the weights -/

/-- **Extraction on the support of the weights.** In
`tsum_ite_eq_zero_of_moments_of_wellFounded` only the moduli of atoms of nonzero weight matter. -/
theorem tsum_ite_eq_zero_of_moments_of_wellFounded_supp {T : Type*} {q w : T → ℂ}
    (hq : Summable fun τ => ‖q τ‖) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ τ, ‖w τ‖ ≤ B)
    (hm : ∀ n : ℕ, ∑' τ, q τ * w τ ^ n = 0) {c₀ : ℂ} (hc₀ : c₀ ≠ 0)
    (hwf : {x : ℝ | ∃ τ, q τ ≠ 0 ∧ ‖w τ‖ = x ∧ ‖c₀‖ ≤ x}.WellFoundedOn (· > ·)) :
    ∑' τ, (if w τ = c₀ then q τ else 0) = 0 := by
  set w' : T → ℂ := fun τ => if q τ = 0 then 0 else w τ
  have hc₀pos : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
  have h := tsum_ite_eq_zero_of_moments_of_wellFounded (w := w') hq (B := B)
    (fun τ => by by_cases h : q τ = 0 <;> simp [w', h, hB0, hB τ])
    (fun n => (tsum_congr fun τ => by by_cases h : q τ = 0 <;> simp [w', h]).trans (hm n)) hc₀
    (hwf.subset fun x ⟨τ, hτ, hx⟩ => by
      by_cases h : q τ = 0
      · simp only [w', if_pos h, norm_zero] at hτ
        exact absurd (hτ ▸ hx) (not_le.mpr hc₀pos)
      · exact ⟨τ, h, by simpa [w', h] using hτ, hx⟩)
  refine (tsum_congr fun τ => ?_).trans h
  by_cases h : q τ = 0 <;> simp [w', h]

/-- Moduli `e^{ℓ(σ − ½)}` over a well-founded set of levels form a well-founded set. -/
theorem wellFoundedOn_moduli_of_levels {ℓ : ℝ} (hℓ : 0 < ℓ) {S : Set ℝ}
    (hwf : S.WellFoundedOn (· > ·)) {T : Type*} (P : T → Prop) (w : T → ℂ) {c : ℝ}
    (hw : ∀ τ, P τ → c ≤ ‖w τ‖ → ∃ σ ∈ S, ‖w τ‖ = Real.exp (ℓ * (σ - 1 / 2))) :
    {x : ℝ | ∃ τ, P τ ∧ ‖w τ‖ = x ∧ c ≤ x}.WellFoundedOn (· > ·) := by
  have hmono : StrictMono fun σ : ℝ => Real.exp (ℓ * (σ - 1 / 2)) := fun a b hab =>
    Real.exp_lt_exp.mpr (by nlinarith)
  have himg : ((fun σ : ℝ => Real.exp (ℓ * (σ - 1 / 2))) '' S).WellFoundedOn (· > ·) :=
    Set.wellFoundedOn_image.mpr (hwf.mono' fun a _ b _ h => hmono.lt_iff_lt.mp h)
  refine himg.mono le_rfl ?_
  rintro x ⟨τ, hP, rfl, hx⟩
  obtain ⟨σ, hσ, he⟩ := hw τ hP hx
  exact ⟨σ, hσ, he.symm⟩

/-- The real parts, at or above `Re ρ`, of the right zeros `τ` at which the test does not vanish at
`γ_τ` or at `γ_{1−τ̄}`: the levels the tower of `g` actually reads. -/
def activeLevels (Z : ZeroConfig) (g : ℝ → ℂ) (ρ : ℂ) : Set ℝ :=
  {σ | ∃ τ ∈ rightZeros Z, (paperFT g (gammaOf τ) ≠ 0 ∨ paperFT g (gammaOf (reflect τ)) ≠ 0) ∧
    τ.re = σ ∧ ρ.re ≤ σ}

/-- **Class separation above a well-founded active level.** As `classSum_eq_zero_of_wellFounded`,
with well-foundedness required only of the levels at which `g` is nonzero. -/
theorem classSum_eq_zero_of_activeWellFounded (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {ρ : ℂ}
    (hρ : ρ ∈ rightZeros Z) (hwf : (activeLevels Z g ρ).WellFoundedOn (· > ·))
    (a : ℓ²(Z.carrier, ℂ)) (ha : ∀ k : ℤ, inner ℂ (towerVec Z hZ hg hgc ℓ k) a = 0) :
    (∑' τ : Z.carrier,
        (if frobEig ℓ τ = frobEig ℓ ρ then conj (zeroCoord Z g τ) * a τ else 0)) = 0 ∧
      ∑' τ : Z.carrier, (if frobEig ℓ τ = reflEig (frobEig ℓ ρ) then
        conj (zeroCoord Z g τ) * a τ else 0) = 0 := by
  have hb1 : 1 < ‖frobEig ℓ ρ‖ := (one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2
  have hb0 : frobEig ℓ ρ ≠ 0 := frobEig_ne_zero ℓ ρ
  have hq := summable_conj_zeroCoord_mul Z hZ hg hgc a
  have hmom := tsum_mul_conj_frobEig_zpow_eq_zero Z hZ hg hgc ℓ a ha
  have hFT : ∀ τ : Z.carrier, conj (zeroCoord Z g τ) * a τ ≠ 0 → paperFT g (gammaOf τ) ≠ 0 :=
    fun τ h hz => h (by simp [zeroCoord, hz])
  have hB0 : 0 ≤ Real.exp (ℓ / 2) := (Real.exp_pos _).le
  constructor
  · -- the outer class, from the top down
    have hw := wellFoundedOn_moduli_of_levels hℓ hwf
      (fun τ : Z.carrier => conj (zeroCoord Z g τ) * a τ ≠ 0)
      (fun τ : Z.carrier => conj (frobEig ℓ τ)) (c := ‖conj (frobEig ℓ ρ)‖) fun τ hP hτ => by
        simp only [Complex.norm_conj] at hτ
        have hre := (norm_frobEig_le_iff hℓ τ ρ).mp hτ
        refine ⟨(τ : ℂ).re, ⟨τ, ⟨τ.2, hρ.2.trans_le hre⟩, Or.inl (hFT τ hP), rfl, hre⟩, ?_⟩
        simp only [Complex.norm_conj, norm_frobEig]
    have h := tsum_ite_eq_zero_of_moments_of_wellFounded_supp hq hB0
      (w := fun τ : Z.carrier => conj (frobEig ℓ τ)) (norm_conj_frobEig_le Z hℓ)
      (fun n => (tsum_congr fun τ => by rw [zpow_natCast]).trans (hmom n))
      ((map_ne_zero (starRingEnd ℂ)).mpr hb0) hw
    simpa only [(starRingEnd ℂ).injective.eq_iff] using h
  · -- the reflected class, from the bottom up
    have e : ∀ β : ℂ, (conj β)⁻¹ = frobEig ℓ ρ ↔ β = reflEig (frobEig ℓ ρ) := fun β => by
      constructor
      · intro h; rw [reflEig, ← h, map_inv₀, Complex.conj_conj, inv_inv]
      · intro h; rw [h, reflEig, map_inv₀, Complex.conj_conj, inv_inv]
    have hw := wellFoundedOn_moduli_of_levels hℓ hwf
      (fun τ : Z.carrier => conj (zeroCoord Z g τ) * a τ ≠ 0)
      (fun τ : Z.carrier => (conj (frobEig ℓ τ))⁻¹) (c := ‖frobEig ℓ ρ‖) fun τ hP hτ => by
        have hτ' : ‖frobEig ℓ ρ‖ ≤ ‖frobEig ℓ (reflect τ)‖ := by
          simpa only [frobEig_reflect] using hτ
        have hre := (norm_frobEig_le_iff hℓ (reflect (τ : ℂ)) ρ).mp hτ'
        refine ⟨(reflect (τ : ℂ)).re, ⟨reflect τ, ⟨Z.reflect_mem _ τ.2, hρ.2.trans_le hre⟩,
          Or.inr (by rw [reflect_reflect]; exact hFT τ hP), rfl, hre⟩, ?_⟩
        rw [← norm_frobEig, frobEig_reflect]
    have h := tsum_ite_eq_zero_of_moments_of_wellFounded_supp hq hB0
      (w := fun τ : Z.carrier => (conj (frobEig ℓ τ))⁻¹) (norm_inv_conj_frobEig_le Z hℓ)
      (fun n => (tsum_congr fun τ => by rw [zpow_neg, zpow_natCast, inv_pow]).trans
        (hmom (-(n : ℤ))))
      hb0 hw
    simpa only [e] using h

/-- **Attainment above well-founded active levels.** Finitely many visible eigenvalues, each above
a level whose active part is well-founded, are seen together by one window of the tower. -/
theorem card_le_towerDefect_of_activeWellFounded (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (O : Finset ℂ) (hO : ∀ b ∈ O, b ∈ visibleSet Z g ℓ)
    (hwf : ∀ b ∈ O, ∃ ρ ∈ rightZeros Z, frobEig ℓ ρ = b ∧
      (activeLevels Z g ρ).WellFoundedOn (· > ·)) :
    ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g ℓ K) :=
  exists_towerGram_negIndex_ge_of_closure Z hZ hg hgc hℓ O hO fun b hb => by
    obtain ⟨ρ, hρ, rfl, hw⟩ := hwf b hb
    exact eigTarget_mem_closure_of_classSum Z hZ hg hgc _ fun a ha =>
      classSum_eq_zero_of_activeWellFounded Z hZ hg hgc hℓ hρ hw a ha

/-! ### 3. Deep-sparse configurations are one-prime complete -/

/-- A configuration is **deep-sparse** when, at every depth `σ > ½`, the right zeros of real part
`≥ σ` have convergence exponent below one: `Σ |γ_τ|^{-s} < ∞` for some `0 < s < 1`. -/
def DeepSparse (Z : ZeroConfig) : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → ∃ s : ℝ, 0 < s ∧ s < 1 ∧
    Summable fun τ : ↥{τ : ℂ | τ ∈ rightZeros Z ∧ σ ≤ τ.re} => ‖gammaOf (τ : ℂ)‖⁻¹ ^ s

theorem norm_gammaOf_reflect (τ : ℂ) : ‖gammaOf (reflect τ)‖ = ‖gammaOf τ‖ := by
  rw [gammaOf_reflect, Complex.norm_conj]

theorem gammaOf_ne_zero_of_re_ne {τ : ℂ} (h : τ.re ≠ 1 / 2) : gammaOf τ ≠ 0 := fun h0 =>
  h (by linarith [SquareRootThreshold.im_gammaOf τ, congrArg Complex.im h0, Complex.zero_im])

/-- **Killing a sparse set of right zeros.** If `A` is a set of points right of the line with
`Σ_{τ ∈ A} |γ_τ|^{-s} < ∞` for some `0 < s < 1`, a `C²` compactly supported test vanishes at `γ_τ`
and `γ_{1−τ̄}` for every `τ ∈ A`, and at no other non-real point. -/
theorem exists_test_killing (A : Set ℂ) (hA : ∀ τ ∈ A, 1 / 2 < τ.re) (hAc : A.Countable)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hsum : Summable fun τ : A => ‖gammaOf (τ : ℂ)‖⁻¹ ^ s) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∀ τ ∈ A, paperFT g (gammaOf τ) = 0 ∧ paperFT g (gammaOf (reflect τ)) = 0) ∧
      ∀ w : ℂ, w.im ≠ 0 → (∀ τ ∈ A, w ≠ gammaOf τ ∧ w ≠ gammaOf (reflect τ)) →
        paperFT g w ≠ 0 := by
  haveI : Countable A := hAc.to_subtype
  set a : A ⊕ A → ℂ := Sum.elim (fun τ => gammaOf (τ : ℂ)) fun τ => gammaOf (reflect (τ : ℂ))
    with ha_def
  have ha : ∀ i, a i ≠ 0 := by
    rintro (τ | τ)
    · exact gammaOf_ne_zero_of_re_ne (hA τ τ.2).ne'
    · refine gammaOf_ne_zero_of_re_ne ?_
      rw [re_reflect]; linarith [hA τ τ.2]
  have hsum' : Summable fun τ : A => ‖gammaOf (reflect (τ : ℂ))‖⁻¹ ^ s := by
    simpa only [norm_gammaOf_reflect] using hsum
  have hsa : Summable fun i => ‖a i‖⁻¹ ^ s := Summable.sum _ hsum hsum'
  obtain ⟨g, hg, hgc, hz, hnz⟩ := exists_annihilating_test_of_countable hs0 hs1 ha hsa
  refine ⟨g, hg, hgc, fun τ hτ => ⟨hz (Sum.inl ⟨τ, hτ⟩), hz (Sum.inr ⟨τ, hτ⟩)⟩,
    fun w hw hwA => hnz w hw ?_⟩
  rintro (τ | τ)
  · exact (hwA τ τ.2).1
  · exact (hwA τ τ.2).2

/-- **A test killing the deep zeros of a deep-sparse configuration.** Given a set `F` of right
zeros and a depth `σ₀ > ½`, a `C²` compactly supported test vanishes at `γ_τ` and `γ_{1−τ̄}` for
every right zero `τ ∉ F` with `Re τ ≥ σ₀`, and at neither point for `τ ∈ F`. -/
theorem exists_test_killing_deep_zeros (Z : ZeroConfig) (hsp : DeepSparse Z) {σ₀ : ℝ}
    (hσ₀ : 1 / 2 < σ₀) (F : Set ℂ) (hF : ∀ τ ∈ F, τ ∈ rightZeros Z) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∀ τ ∈ rightZeros Z, σ₀ ≤ τ.re → τ ∉ F →
        paperFT g (gammaOf τ) = 0 ∧ paperFT g (gammaOf (reflect τ)) = 0) ∧
      ∀ τ ∈ F, paperFT g (gammaOf τ) ≠ 0 ∧ paperFT g (gammaOf (reflect τ)) ≠ 0 := by
  obtain ⟨s, hs0, hs1, hsum⟩ := hsp σ₀ hσ₀
  set S : Set ℂ := {τ : ℂ | τ ∈ rightZeros Z ∧ σ₀ ≤ τ.re} with hS
  set A : Set ℂ := S \ F with hA
  have hAS : A ⊆ S := Set.sdiff_subset
  have hAr : ∀ τ ∈ A, τ ∈ rightZeros Z := fun τ hτ => (hAS hτ).1
  have hAc : A.Countable :=
    (SquareRootThreshold.countable_carrier Z).mono fun τ hτ => (hAr τ hτ).1
  have hsumA : Summable fun τ : A => ‖gammaOf (τ : ℂ)‖⁻¹ ^ s := by
    simpa only [Function.comp_def, Set.coe_inclusion] using
      hsum.comp_injective (Set.inclusion_injective hAS)
  obtain ⟨g, hg, hgc, hz, hnz⟩ :=
    exists_test_killing A (fun τ hτ => (hAr τ hτ).2) hAc hs0 hs1 hsumA
  have hmemA : ∀ τ ∈ rightZeros Z, σ₀ ≤ τ.re → τ ∉ F → τ ∈ A := fun τ hτ hle hτF =>
    ⟨⟨hτ, hle⟩, hτF⟩
  have hAF : ∀ τ ∈ A, τ ∉ F := fun τ hτ => hτ.2
  refine ⟨g, hg, hgc, fun τ hτ hle hτF => hz τ (hmemA τ hτ hle hτF), fun τ₀ hτ₀ => ?_⟩
  have hre := (hF τ₀ hτ₀).2
  constructor
  · refine hnz _
      (by rw [SquareRootThreshold.im_gammaOf]; exact (by linarith : 1 / 2 - τ₀.re < 0).ne)
      fun τ hτ => ⟨fun h => hAF τ hτ (by rw [← gammaOf_injective h]; exact hτ₀), fun h => ?_⟩
    have h' := congrArg Complex.im h
    rw [SquareRootThreshold.im_gammaOf, SquareRootThreshold.im_gammaOf, re_reflect] at h'
    linarith [(hAr τ hτ).2]
  · refine hnz _ (by
        rw [SquareRootThreshold.im_gammaOf, re_reflect]
        exact (by linarith : 0 < 1 / 2 - (1 - τ₀.re)).ne')
      fun τ hτ => ⟨fun h => ?_, fun h => hAF τ hτ ?_⟩
    · have h' := congrArg Complex.im h
      rw [SquareRootThreshold.im_gammaOf, SquareRootThreshold.im_gammaOf, re_reflect] at h'
      linarith [(hAr τ hτ).2]
    · have h'' : τ₀ = τ := by
        rw [← reflect_reflect τ₀, gammaOf_injective h, reflect_reflect]
      rw [← h'']; exact hτ₀

/-- **A single surviving term.** If `g` is nonzero at `γ_ρ` and `γ_{1−ρ̄}` for a right zero `ρ` and
vanishes at `γ_τ` for every other zero `τ` with the same eigenvalue, the weight of `p^{ρ−½}` is the
nonzero term `X_ρ(g) conj X_{1−ρ̄}(g)`. -/
theorem frobWeight_ne_zero_of_single (Z : ZeroConfig) {g : ℝ → ℂ} {ℓ : ℝ} {ρ b : ℂ}
    (hρ : ρ ∈ rightZeros Z) (hb : frobEig ℓ ρ = b)
    (hkeep : paperFT g (gammaOf ρ) ≠ 0 ∧ paperFT g (gammaOf (reflect ρ)) ≠ 0)
    (hkill : ∀ τ ∈ Z.carrier, τ ≠ ρ → frobEig ℓ τ = b → paperFT g (gammaOf τ) = 0) :
    frobWeight Z g ℓ b ≠ 0 := by
  have hsingle : ∀ τ : Z.carrier, τ ≠ ⟨ρ, hρ.1⟩ →
      (if frobEig ℓ τ = b then
        zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) else 0) = 0 := by
    intro τ hτ
    split_ifs with he
    · have h0 := hkill τ τ.2 (fun h => hτ (Subtype.ext h)) he
      simp [zeroCoord, h0]
    · rfl
  rw [frobWeight, tsum_eq_single _ hsingle,
    if_pos (show frobEig ℓ ((⟨ρ, hρ.1⟩ : Z.carrier) : ℂ) = b from hb)]
  have hm : ∀ τ : Z.carrier, (Real.sqrt (Z.mult τ) : ℂ) ≠ 0 := fun τ =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Z.one_le_mult _ τ.2)))
  exact mul_ne_zero (mul_ne_zero (hm _) hkeep.1) ((map_ne_zero _).mpr (mul_ne_zero (hm _) hkeep.2))

/-- If `g` kills every right zero of depth `≥ σ₀` outside a finite set `F`, the active levels above
any level `≥ σ₀` are real parts of points of `F`, hence well-founded. -/
theorem activeLevels_wellFounded_of_kill (Z : ZeroConfig) {g : ℝ → ℂ} {F : Finset ℂ} {σ₀ : ℝ}
    (hkill : ∀ τ ∈ rightZeros Z, σ₀ ≤ τ.re → τ ∉ F →
      paperFT g (gammaOf τ) = 0 ∧ paperFT g (gammaOf (reflect τ)) = 0)
    {ρ : ℂ} (hρ : σ₀ ≤ ρ.re) : (activeLevels Z g ρ).WellFoundedOn (· > ·) := by
  refine (((F.image Complex.re).finite_toSet).subset ?_).wellFoundedOn
  rintro σ ⟨τ, hτ, hnz, rfl, hle⟩
  by_cases hτF : τ ∈ F
  · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hτF)
  · have h0 := hkill τ hτ (hρ.trans hle) hτF
    exact absurd hnz (by simp [h0.1, h0.2])

/-- **One prime sees every finite set of outer eigenvalues of a deep-sparse configuration.** For
each finite set `O` of outer Frobenius eigenvalues at scale `ℓ` there are a `C²` compactly
supported test and a window of its tower with at least `#O` negative squares. The test kills every
right zero at least as deep as the shallowest chosen representative, except the representatives:
the weight of each `b ∈ O` is then a single nonzero term and the active levels are finite. -/
theorem exists_test_card_le_towerDefect (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) {ℓ : ℝ} (hℓ : 0 < ℓ) (O : Finset ℂ) (hO : ∀ b ∈ O, b ∈ outerEig Z ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ∃ K : Finset ℤ, O.card ≤ hermNegIndex (towerGram Z g ℓ K) := by
  rcases O.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ∅, by simp⟩
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
  obtain ⟨g, hg, hgc, hkill, hkeep⟩ := exists_test_killing_deep_zeros Z hsp hσ₀ ↑F hFr
  have hrF : ∀ b ∈ O, r b ∈ F := fun b hb => Finset.mem_image_of_mem r hb
  refine ⟨g, hg, hgc, card_le_towerDefect_of_activeWellFounded Z hZ hg hgc hℓ O
    (fun b hb => ⟨⟨r b, hr b hb, hrb b hb⟩, ?_⟩)
    fun b hb => ⟨r b, hr b hb, hrb b hb, activeLevels_wellFounded_of_kill Z hkill (hσ₀le b hb)⟩⟩
  refine frobWeight_ne_zero_of_single Z (hr b hb) (hrb b hb) (hkeep _ (hrF b hb))
    fun τ hτ hne he => ?_
  -- another zero with eigenvalue `b` lies on the level of `r b` and is not a representative
  have hre : τ.re = (r b).re := re_eq_of_norm_frobEig_eq hℓ (by rw [he, hrb b hb])
  have hτr : τ ∈ rightZeros Z := ⟨hτ, by rw [hre]; exact (hr b hb).2⟩
  refine (hkill τ hτr (by rw [hre]; exact hσ₀le b hb) fun hm => hne ?_).1
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hm
  have : b' = b := by rw [← hrb b' hb', he]
  rw [this]

/-- **The one-prime tower law for deep-sparse configurations.** Some window of the tower of some
test has `n` negative squares iff there are at least `n` distinct outer eigenvalues. -/
theorem deepSparse_tower_law (Z : ZeroConfig) (hZ : TemperedConfig Z) (hsp : DeepSparse Z)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    (∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
      (n : ℕ∞) ≤ (outerEig Z ℓ).encard := by
  constructor
  · rintro ⟨g, hg, hgc, K, hK⟩
    exact (ENat.coe_le_coe.mpr hK).trans
      (((wfVisibleSet_sandwich_and_infinite_law Z hZ hg hgc hℓ).2.1 K).1.trans
        ((wfVisibleSet_sandwich_and_infinite_law Z hZ hg hgc hℓ).2.1 K).2)
  · intro hn
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hn
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htc
    obtain ⟨g, hg, hgc, K, hK⟩ := exists_test_card_le_towerDefect Z hZ hsp hℓ htfin.toFinset
      fun b hb => hts (htfin.mem_toFinset.mp hb)
    have hcard : htfin.toFinset.card = n := by
      have := htfin.encard_eq_coe_toFinset_card
      rw [htc] at this
      exact_mod_cast this.symm
    exact ⟨g, hg, hgc, K, hcard ▸ hK⟩

/-! ### 4. `ζ` is deep-sparse -/

/-- Distinct nontrivial zeros in a height box inject into its zero copies. -/
theorem card_le_ncard_zeroHeightBox {σ T : ℝ} (v : Finset ℂ)
    (hv : ∀ z ∈ v, z ∈ zetaZeroConfig.carrier ∧ σ ≤ z.re ∧ T ≤ z.im ∧ z.im ≤ 2 * T) :
    v.card ≤ (_root_.RHTower.zeroHeightBox σ T).ncard := by
  set v' : Finset zetaZeroConfig.carrier := v.subtype (· ∈ zetaZeroConfig.carrier)
  have hv' : v'.card = v.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem fun z hz => (hv z hz).1]
  have hinj : Function.Injective carrierCopy := fun ρ₁ ρ₂ h => Subtype.ext (by
    rw [← carrierCopy_val ρ₁, ← carrierCopy_val ρ₂, h])
  rw [← hv', ← Finset.card_map ⟨carrierCopy, hinj⟩, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (_root_.RHTower.zeroHeightBox_finite σ T)
  intro q hq
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_map.mp hq
  have h := hv ρ (Finset.mem_subtype.mp hρ)
  simp only [_root_.RHTower.zeroHeightBox, Set.mem_setOf_eq, Function.Embedding.coeFn_mk,
    carrierCopy_val]
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-- Distinct nontrivial zeros with `T ≤ |γ| ≤ 2T` number at most twice the box count. -/
theorem card_le_two_mul_ncard_zeroHeightBox {σ T : ℝ} (v : Finset ℂ)
    (hv : ∀ z ∈ v, z ∈ zetaZeroConfig.carrier ∧ σ ≤ z.re ∧ T ≤ |z.im| ∧ |z.im| ≤ 2 * T)
    (hT : 0 < T) :
    v.card ≤ 2 * (_root_.RHTower.zeroHeightBox σ T).ncard := by
  rw [← Finset.card_filter_add_card_filter_not (fun z : ℂ => 0 < z.im), two_mul]
  refine add_le_add (card_le_ncard_zeroHeightBox _ fun z hz => ?_) ?_
  · obtain ⟨hz, hpos⟩ := Finset.mem_filter.mp hz
    have h := hv z hz
    rw [abs_of_pos hpos] at h
    exact h
  · rw [← Finset.card_image_of_injective _ (starRingEnd ℂ).injective]
    refine card_le_ncard_zeroHeightBox _ fun z hz => ?_
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hw, hneg⟩ := Finset.mem_filter.mp hw
    have h := hv w hw
    have hlt : w.im < 0 := by
      rcases (not_lt.mp hneg).lt_or_eq with h' | h'
      · exact h'
      · rw [h', abs_zero] at h; linarith [h.2.2.1]
    rw [abs_of_neg hlt] at h
    exact ⟨_root_.RHTower.conj_mem_zetaZeroConfig h.1, by simpa using h.2.1,
      by simpa using h.2.2.1, by simpa using h.2.2.2⟩

/-- **Dyadic summation of a zero-density bound.** If every height box `[T, 2T]`, `T ≥ T₀`, holds at
most `D (1 + log T)^B T^E` zero copies of real part `≥ σ`, then for `s > E` every finite set of
distinct nontrivial zeros with `Re ≥ σ` and `|γ| ≥ T₀` has `Σ |γ_τ|^{-s}` bounded uniformly. -/
theorem sum_norm_gammaOf_rpow_le_of_density {σ E s D T₀ : ℝ} {B : ℕ} (hT₀ : 1 ≤ T₀)
    (hD : 0 ≤ D) (hs : 0 ≤ s) (hEs : E < s)
    (hbox : ∀ T : ℝ, T₀ ≤ T →
      ((_root_.RHTower.zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ E)
    (v : Finset ℂ) (hv : ∀ z ∈ v, z ∈ zetaZeroConfig.carrier ∧ σ ≤ z.re ∧ T₀ ≤ |z.im|) :
    ∑ z ∈ v, ‖gammaOf z‖⁻¹ ^ s ≤
      2 * D * (1 + (B + 1) / ((s - E) / 2)) ^ B * (1 / (1 - (2 : ℝ) ^ (-((s - E) / 2)))) := by
  set e : ℝ := (s - E) / 2 with he
  have he0 : 0 < e := by rw [he]; linarith
  have hT₀0 : 0 < T₀ := by linarith
  set P : ℝ := (1 + (B + 1) / e) ^ B with hP
  have hP0 : 0 ≤ P := by positivity
  set k : ℂ → ℕ := fun z => Nat.log 2 ⌊|z.im| / T₀⌋₊
  set Tk : ℕ → ℝ := fun j => T₀ * 2 ^ j
  have hTk0 : ∀ j, 0 < Tk j := fun j => by positivity
  have hTk1 : ∀ j, T₀ ≤ Tk j := fun j => le_mul_of_one_le_right hT₀0.le (one_le_pow₀ (by norm_num))
  -- the dyadic index brackets `|γ|`
  have hk : ∀ z ∈ v, Tk (k z) ≤ |z.im| ∧ |z.im| ≤ 2 * Tk (k z) := by
    intro z hz
    have h := _root_.RHTower.dyadicHeightIndex_bounds hT₀0 (q := carrierCopy ⟨z, (hv z hz).1⟩)
      (by rw [carrierCopy_val]; exact (hv z hz).2.2)
    simpa only [_root_.RHTower.dyadicHeightIndex, carrierCopy_val] using h
  -- each dyadic shell carries `≤ 2 D P T^{-e}`
  have hshell : ∀ j, ∑ z ∈ v with k z = j, ‖gammaOf z‖⁻¹ ^ s ≤ 2 * D * P * Tk j ^ (-e) := by
    intro j
    have hterm : ∀ z ∈ v.filter (k · = j), ‖gammaOf z‖⁻¹ ^ s ≤ Tk j ^ (-s) := by
      intro z hz
      obtain ⟨hzv, rfl⟩ := Finset.mem_filter.mp hz
      have hlow : Tk (k z) ≤ ‖gammaOf z‖ := (hk z hzv).1.trans (by
        have : |z.im| = |(gammaOf z).re| := by simp [gammaOf]
        rw [this]; exact Complex.abs_re_le_norm _)
      rw [Real.rpow_neg (hTk0 _).le, ← Real.inv_rpow (hTk0 _).le]
      exact Real.rpow_le_rpow (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ (hTk0 _) hlow) hs
    have hcard : ((v.filter (k · = j)).card : ℝ) ≤
        2 * ((_root_.RHTower.zeroHeightBox σ (Tk j)).ncard : ℝ) := by
      have := card_le_two_mul_ncard_zeroHeightBox (σ := σ) (T := Tk j) (v.filter (k · = j))
        (fun z hz => by
          obtain ⟨hzv, hkz⟩ := Finset.mem_filter.mp hz
          have h := hk z hzv
          rw [hkz] at h
          exact ⟨(hv z hzv).1, (hv z hzv).2.1, h.1, h.2⟩) (hTk0 j)
      exact_mod_cast this
    have hlog := _root_.RHTower.one_add_log_pow_le_rpow B he0 (hT₀.trans (hTk1 j))
    have hTs : 0 ≤ Tk j ^ (-s) := Real.rpow_nonneg (hTk0 j).le _
    calc ∑ z ∈ v with k z = j, ‖gammaOf z‖⁻¹ ^ s ≤ ∑ z ∈ v with k z = j, Tk j ^ (-s) :=
          Finset.sum_le_sum hterm
      _ = ((v.filter (k · = j)).card : ℝ) * Tk j ^ (-s) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (D * (P * Tk j ^ e) * Tk j ^ E) * Tk j ^ (-s) := by
          refine mul_le_mul_of_nonneg_right (hcard.trans ?_) hTs
          refine mul_le_mul_of_nonneg_left ((hbox _ (hTk1 j)).trans ?_) (by norm_num)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hD)
            (Real.rpow_nonneg (hTk0 j).le _)
      _ = 2 * D * P * (Tk j ^ e * Tk j ^ E * Tk j ^ (-s)) := by ring
      _ = 2 * D * P * Tk j ^ (-e) := by
          rw [← Real.rpow_add (hTk0 j), ← Real.rpow_add (hTk0 j)]
          congr 2
          rw [he]; ring
  -- sum the shells
  have hmaps : ∀ z ∈ v, k z ∈ v.image k := fun z hz => Finset.mem_image_of_mem k hz
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set N : ℕ := (v.image k).sup id + 1
  have hsub : v.image k ⊆ Finset.range N := fun j hj =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
  have hc0 : 0 ≤ 2 * D * P := by positivity
  calc ∑ j ∈ v.image k, ∑ z ∈ v with k z = j, ‖gammaOf z‖⁻¹ ^ s
        ≤ ∑ j ∈ v.image k, 2 * D * P * Tk j ^ (-e) := Finset.sum_le_sum fun j _ => hshell j
    _ ≤ ∑ j ∈ Finset.range N, 2 * D * P * Tk j ^ (-e) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
          mul_nonneg hc0 (Real.rpow_nonneg (hTk0 j).le _)
    _ = 2 * D * P * ∑ j ∈ Finset.range N, Tk j ^ (-e) := by rw [Finset.mul_sum]
    _ ≤ 2 * D * P * (1 / (1 - (2 : ℝ) ^ (-e))) :=
        mul_le_mul_of_nonneg_left (_root_.RHTower.sum_dyadic_rpow_neg_le hT₀ he0 N) hc0

/-- **`ζ` is deep-sparse.** At depth `σ ∈ (½, ¾]` the Ingham–Huxley estimate bounds the height box
`[T, 2T]` by `T^{(3/(2−σ) + ε)(1−σ)}` up to logarithms, an exponent below one; summing over dyadic
boxes gives `Σ_{Re τ ≥ σ} |γ_τ|^{-s} < ∞` for `s` between that exponent and one. Deeper levels are
subsets. -/
theorem deepSparse_zeta : DeepSparse zetaZeroConfig := by
  intro σ hσ
  set σ' : ℝ := min σ (3 / 4)
  have hσ'1 : 1 / 2 < σ' := lt_min hσ (by norm_num)
  have hσ'2 : σ' ≤ 3 / 4 := min_le_right _ _
  have hσ'σ : σ' ≤ σ := min_le_left _ _
  have hA : _root_.RHTower.inghamHuxleyExponent σ' = 3 / (2 - σ') := by
    unfold _root_.RHTower.inghamHuxleyExponent; rw [if_pos hσ'2]
  have hkey : 3 / (2 - σ') * (1 - σ') < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  have hkey0 : 0 ≤ 3 / (2 - σ') * (1 - σ') :=
    mul_nonneg (div_nonneg (by norm_num) (by linarith)) (by linarith)
  set ε : ℝ := (1 - 3 / (2 - σ') * (1 - σ')) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hε1 : ε ≤ 1 := by rw [hεdef]; linarith
  obtain ⟨D, hD, B, T₀, hT₀, hbox⟩ :=
    _root_.RHTower.exists_zeroHeightBox_ncard_le_ingham_huxley hσ'1 (by linarith) hε hε1
  rw [hA] at hbox
  have hE1 : (3 / (2 - σ') + ε) * (1 - σ') < 1 := by
    have h1 : (3 / (2 - σ') + ε) * (1 - σ') = 3 / (2 - σ') * (1 - σ') + ε * (1 - σ') := by ring
    have h2 : ε * (1 - σ') < ε := by nlinarith
    rw [h1]; linarith
  have hE0 : 0 ≤ (3 / (2 - σ') + ε) * (1 - σ') :=
    mul_nonneg (add_nonneg (div_nonneg (by norm_num) (by linarith)) hε.le) (by linarith)
  set E : ℝ := (3 / (2 - σ') + ε) * (1 - σ') with hEdef
  set s : ℝ := (E + 1) / 2 with hsdef
  refine ⟨s, by linarith, by linarith, ?_⟩
  set L : Finset ℂ := (finite_rightZeros_of_abs_im_le zetaZeroConfig T₀).toFinset
  refine summable_of_sum_le (c := ∑ z ∈ L, ‖gammaOf z‖⁻¹ ^ s +
      2 * D * (1 + (B + 1) / ((s - E) / 2)) ^ B * (1 / (1 - (2 : ℝ) ^ (-((s - E) / 2)))))
    (fun τ => Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _) fun u => ?_
  set v : Finset ℂ := u.map (Function.Embedding.subtype _)
  have hv : ∀ z ∈ v, z ∈ rightZeros zetaZeroConfig ∧ σ ≤ z.re := fun z hz => by
    obtain ⟨τ, -, rfl⟩ := Finset.mem_map.mp hz
    exact τ.2
  have hsum_eq : ∑ τ ∈ u, ‖gammaOf (τ : ℂ)‖⁻¹ ^ s = ∑ z ∈ v, ‖gammaOf z‖⁻¹ ^ s :=
    (Finset.sum_map u (Function.Embedding.subtype _) fun z => ‖gammaOf z‖⁻¹ ^ s).symm
  refine hsum_eq.le.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not v (fun z => |z.im| < T₀)]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_) fun z _ _ =>
      Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
    obtain ⟨hzv, hlt⟩ := Finset.mem_filter.mp hz
    exact (Set.Finite.mem_toFinset _).mpr ⟨(hv z hzv).1, hlt.le⟩
  · refine sum_norm_gammaOf_rpow_le_of_density hT₀ hD (by linarith) (by linarith) hbox _
      fun z hz => ?_
    obtain ⟨hzv, hge⟩ := Finset.mem_filter.mp hz
    exact ⟨(hv z hzv).1.1, hσ'σ.trans (hv z hzv).2, not_lt.mp hge⟩

/-! ### 5. One prime suffices for `ζ` -/

/-- **The one-prime tower law for `ζ`.** At every prime `p`, some window of the `p`-tower of some
test carries `n` negative squares of Weil's form iff `ζ` has at least `n` distinct outer
eigenvalues `p^{ρ−½}`. -/
theorem zeta_one_prime_tower_law {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram zetaZeroConfig g (Real.log p) K)) ↔
      (n : ℕ∞) ≤ (outerEig zetaZeroConfig (Real.log p)).encard :=
  deepSparse_tower_law _ temperedConfig_zetaZeroConfig deepSparse_zeta
    (Real.log_pos (by exact_mod_cast hp.one_lt)) n

/-- **RH is positivity on the towers of one prime.** For any fixed prime `p`, RH holds iff Weil's
form (prime side, von Mangoldt weights) is positive semidefinite on every finite window of every
Hecke tower `g(· − k log p)`. -/
theorem riemannHypothesis_iff_onePrime_towers {p : ℕ} (hp : p.Prime) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g → ∀ K : Finset ℤ,
      hermNegIndex (weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        fun k : K => translate (((k : ℤ) : ℝ) * Real.log p) g) = 0 := by
  have hw : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → HasCompactSupport g → ∀ K : Finset ℤ,
      weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        (fun k : K => translate (((k : ℤ) : ℝ) * Real.log p) g) =
        towerGram zetaZeroConfig g (Real.log p) K := fun g hg hgc K =>
    weilGram_eq_zeroGram _ (fun _ => translate_contDiff hg _)
      (fun _ => translate_hasCompactSupport hgc _)
  rw [← rightZeros_zeta_eq_empty_iff]
  constructor
  · intro hRH g hg hgc K
    rw [hw g hg hgc K]
    by_contra hne
    have h1 := (zeta_one_prime_tower_law hp 1).mp ⟨g, hg, hgc, K, Nat.one_le_iff_ne_zero.mpr hne⟩
    have h0 : outerEig zetaZeroConfig (Real.log p) = ∅ := by simp [outerEig, hRH]
    rw [h0, Set.encard_empty] at h1
    exact absurd h1 (by norm_num)
  · intro hpsd
    by_contra hne
    obtain ⟨ρ, hρ⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨g, hg, hgc, K, hK⟩ := (zeta_one_prime_tower_law hp 1).mpr
      (Set.one_le_encard_iff_nonempty.mpr ⟨_, ρ, hρ, rfl⟩)
    have h := hpsd g hg hgc K
    rw [hw g hg hgc K] at h
    omega

/-- **At most one prime fails to separate an infinite set.** If `S` is infinite, at most one prime
`p` has finitely many eigenvalues `p^{ρ−½}` on `S`: for two such primes the pairs of eigenvalues
take finitely many values, so two distinct points of `S` would collide at both primes. -/
theorem subsingleton_finite_frobEig_image {S : Set ℂ} (hS : S.Infinite) :
    {p : ℕ | p.Prime ∧ (frobEig (Real.log p) '' S).Finite}.Subsingleton := by
  rintro p ⟨hp, hpf⟩ q ⟨hq, hqf⟩
  by_contra hpq
  obtain ⟨x, hx, y, hy, hxy, he⟩ := hS.exists_ne_map_eq_of_mapsTo
    (f := fun τ => (frobEig (Real.log p) τ, frobEig (Real.log q) τ))
    (fun τ hτ => Set.mk_mem_prod (Set.mem_image_of_mem _ hτ) (Set.mem_image_of_mem _ hτ))
    (hpf.prod hqf)
  exact hpq (subsingleton_resonantPrimes hxy ⟨hp, congrArg Prod.fst he⟩ ⟨hq, congrArg Prod.snd he⟩)

/-- **Almost every prime tower carries the whole Hodge defect of `ζ`.** For all but finitely many
primes `p`, some window of the `p`-tower of some test has `n` negative squares iff `ζ` has at least
`n` right zeros, finitely or infinitely many. With infinitely many right zeros at most one prime is
exceptional (`subsingleton_finite_frobEig_image`). -/
theorem zeta_almost_every_prime_tower_law :
    {p : ℕ | p.Prime ∧ ¬ ∀ n : ℕ,
      ((∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
        ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram zetaZeroConfig g (Real.log p) K)) ↔
        (n : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard)}.Finite := by
  have hlaw : ∀ p : ℕ, p.Prime → (outerEig zetaZeroConfig (Real.log p)).encard =
      (rightZeros zetaZeroConfig).encard → ∀ n : ℕ,
      ((∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
        ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram zetaZeroConfig g (Real.log p) K)) ↔
        (n : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard) := fun p hp he n => by
    rw [zeta_one_prime_tower_law hp n, he]
  by_cases hfin : (rightZeros zetaZeroConfig).Finite
  · refine (finite_resonantPrimes_of_finite hfin).subset fun p ⟨hp, hne⟩ =>
      ⟨hp, fun hinj => hne (hlaw p hp (by rw [outerEig, hinj.encard_image]))⟩
  · refine (subsingleton_finite_frobEig_image hfin).finite.subset fun p ⟨hp, hne⟩ => ⟨hp, ?_⟩
    by_contra hinf
    have hinf' : (outerEig zetaZeroConfig (Real.log p)).Infinite := hinf
    exact hne (hlaw p hp (by rw [hinf'.encard_eq, Set.Infinite.encard_eq hfin]))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
