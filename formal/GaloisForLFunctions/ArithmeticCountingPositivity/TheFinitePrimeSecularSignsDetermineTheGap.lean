import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheFullResolvent
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.TheSelectiveMarginIsTwoLogTwo
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonLawsHoldForProfilesOfBoundedVariation

/-!
# Exact finite-prime gaps from arithmetic secular signs

The reciprocal reading classifies every hyperplane gap for an arbitrary
finite prime set. The criterion includes its endpoint through the epsilon
in the uniform gap definition and gives an attained positive greatest gap.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics

open private finiteFlip_mul_self_all from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheConductorCoordinates

local notation "γ" => Real.eulerMascheroniConstant

private theorem finiteFlip_harmonic_sum {N : ℕ} (hN : 1 ≤ N) (F : Finset ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    (∑ k : PrimeHorizonIndex N, finiteFlip F k * u k / Real.sqrt k) =
      Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) * ⟪finiteFlipHorizonVector F N, u⟫ := by
  have hS : 0 < Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) :=
    Real.sqrt_pos.mpr (gaugeHarmonicSum_one_pos hN)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ k : PrimeHorizonIndex N, finiteFlip F k * u k / Real.sqrt k) =
    Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) *
      ∑ k : PrimeHorizonIndex N,
        u k * (finiteFlip F k / Real.sqrt k /
          Real.sqrt (gaugeHarmonicSum (fun _ => 1) N))
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have hk : (0 : ℝ) < (k : ℕ) := by exact_mod_cast (mem_Icc.mp k.property).1
  field_simp [hS.ne', (Real.sqrt_pos.mpr hk).ne']

private theorem prime_quadratic_eq_inner {N : ℕ}
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    dotProduct (⇑u) (Matrix.mulVec (fullPrimeMatrix N) ⇑u) =
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rfl

/-- Twisting is an exact isometry between the harmonic constraint and the
orthogonal complement of the normalized finite-prime vector. -/
private theorem finiteFlip_form_bound_iff {F : Finset ℕ} {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    (∀ u : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪finiteFlipHorizonVector F N, u⟫ = 0 →
      (γ + s) * ‖u‖ ^ 2 ≤ Real.log N * ‖u‖ ^ 2 -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) ↔
      (∀ x : ℕ → ℝ, (∑ n ∈ Icc 1 N, x n / Real.sqrt n) = 0 →
        atomicWeilForm N (fun n => finiteFlip F n * x n) ≤
          (Real.log N - γ - s) * ∑ n ∈ Icc 1 N, x n ^ 2) := by
  constructor
  · intro h x hx
    let u : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
      WithLp.toLp 2 (fun i => finiteFlip F i * x i)
    have hu : ⟪finiteFlipHorizonVector F N, u⟫ = 0 := by
      have hS := (Real.sqrt_pos.mpr (gaugeHarmonicSum_one_pos hN)).ne'
      apply (mul_eq_zero.mp (show Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) *
        ⟪finiteFlipHorizonVector F N, u⟫ = 0 from ?_)).resolve_left hS
      rw [← finiteFlip_harmonic_sum hN F u]
      change (∑ i : PrimeHorizonIndex N, finiteFlip F i * (finiteFlip F i * x i) /
        Real.sqrt i) = 0
      simp_rw [← mul_assoc, finiteFlip_mul_self_all, one_mul]
      exact (sum_coe_sort (Icc 1 N) (fun n => x n / Real.sqrt n)).trans hx
    have hmass : ‖u‖ ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change (∑ i : PrimeHorizonIndex N, (finiteFlip F i * x i) ^ 2) = _
      simp_rw [mul_pow, sq (finiteFlip F _), finiteFlip_mul_self_all, one_mul]
      exact sum_coe_sort (Icc 1 N) (fun n => x n ^ 2)
    have hform : atomicWeilForm N (fun n => finiteFlip F n * x n) =
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫ := by
      calc
        _ = atomicWeilForm N (horizonExtend ⇑u) := atomicWeilForm_congr fun n hn => by
          simp only [horizonExtend, dif_pos hn]
          rfl
        _ = _ := by rw [atomicWeilForm_horizonExtend, prime_quadratic_eq_inner]
    have hb := h u hu
    rw [hmass] at hb
    rw [hform]
    nlinarith only [hb]
  · intro h u hu
    let x : ℕ → ℝ := fun n => finiteFlip F n * horizonExtend ⇑u n
    have hx : (∑ n ∈ Icc 1 N, x n / Real.sqrt n) = 0 := by
      change (∑ n ∈ Icc 1 N, finiteFlip F n * horizonExtend ⇑u n / Real.sqrt n) = 0
      rw [sum_horizonExtend ⇑u (fun n t => finiteFlip F n * t / Real.sqrt n),
        finiteFlip_harmonic_sum hN F u, hu, mul_zero]
    have hmass : (∑ n ∈ Icc 1 N, x n ^ 2) = ‖u‖ ^ 2 := by
      calc
        _ = ∑ n ∈ Icc 1 N, horizonExtend ⇑u n ^ 2 := by
          refine sum_congr rfl fun n _ => ?_
          dsimp only [x]
          rw [mul_pow, sq (finiteFlip F n), finiteFlip_mul_self_all, one_mul]
        _ = ∑ i : PrimeHorizonIndex N, u i ^ 2 := sum_horizonExtend ⇑u (fun _ t => t ^ 2)
        _ = _ := (EuclideanSpace.real_norm_sq_eq u).symm
    have htwist : (fun n => finiteFlip F n * x n) = horizonExtend ⇑u := by
      funext n
      dsimp only [x]
      rw [← mul_assoc, finiteFlip_mul_self_all, one_mul]
    have hb := h x hx
    rw [htwist, atomicWeilForm_horizonExtend, prime_quadratic_eq_inner, hmass] at hb
    nlinarith only [hb]

private theorem finiteFlip_form_iff_resolvent {F : Finset ℕ} {N : ℕ} {s : ℝ}
    (i₀ : PrimeHorizonIndex N)
    (hneg : fullPrimeEnergyEigenvalue N i₀ - γ < s)
    (hpos : ∀ i, i ≠ i₀ → s < fullPrimeEnergyEigenvalue N i - γ)
    (hv : ⟪finiteFlipHorizonVector F N,
      (fullPrimeMatrix_isHermitian N).eigenvectorBasis i₀⟫ ≠ 0) :
    (∀ u : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪finiteFlipHorizonVector F N, u⟫ = 0 →
      (γ + s) * ‖u‖ ^ 2 ≤ Real.log N * ‖u‖ ^ 2 -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) ↔
      finiteFlipFiniteResolvent F N s ≤ 0 := by
  let a : PrimeHorizonIndex N → ℝ := fun i =>
    ⟪finiteFlipHorizonVector F N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫
  let b := γ + s - fullPrimeEnergyEigenvalue N i₀
  let S := ∑ i ∈ univ.erase i₀, a i ^ 2 / (fullPrimeEnergyEigenvalue N i - γ - s)
  have hb : 0 < b := by dsimp only [b]; linarith only [hneg]
  have hn : Real.log N - (fullPrimeMatrix_isHermitian N).eigenvalues i₀ < γ + s := by
    change fullPrimeEnergyEigenvalue N i₀ < γ + s
    linarith only [hneg]
  have hp' : ∀ i, i ≠ i₀ → γ + s < Real.log N - (fullPrimeMatrix_isHermitian N).eigenvalues i := by
    intro i hi
    have hh := hpos i hi
    change γ + s < fullPrimeEnergyEigenvalue N i
    linarith only [hh]
  have he := hermitian_hyperplane_bound_iff (fullPrimeMatrix_isHermitian N)
    (finiteFlipHorizonVector F N) (Real.log N) (γ + s) i₀ hn hp' hv
  have hd (i : PrimeHorizonIndex N) : Real.log N - (fullPrimeMatrix_isHermitian N).eigenvalues i -
      (γ + s) = fullPrimeEnergyEigenvalue N i - γ - s := by
    rw [fullPrimeEnergyEigenvalue]
    ring
  simp only [hd] at he
  rw [he]
  change b * S ≤ a i₀ ^ 2 ↔ finiteFlipFiniteResolvent F N s ≤ 0
  have hhead : fullPrimeEnergyEigenvalue N i₀ - γ - s = -b := by dsimp only [b]; ring
  have hsplit : finiteFlipFiniteResolvent F N s = a i₀ ^ 2 / (-b) + S := by
    rw [finiteFlipFiniteResolvent, ← sum_erase_add _ _ (mem_univ i₀), hhead]
    change S + a i₀ ^ 2 / (-b) = a i₀ ^ 2 / (-b) + S
    ring
  have hscale : b * finiteFlipFiniteResolvent F N s = b * S - a i₀ ^ 2 := by
    rw [hsplit]
    field_simp [hb.ne']
    ring
  constructor
  · intro hpaid
    have hh : b * finiteFlipFiniteResolvent F N s ≤ b * 0 := by
      rw [hscale, mul_zero]
      linarith only [hpaid]
    exact le_of_mul_le_mul_left hh hb
  · intro hF
    have hh := mul_nonpos_of_nonneg_of_nonpos hb.le hF
    rw [hscale] at hh
    linarith only [hh]

private theorem eventually_finiteFlip_form_iff_resolvent (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) {s : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    ∀ᶠ N : ℕ in atTop,
      (∀ u : EuclideanSpace ℝ (PrimeHorizonIndex (N + 1)),
        ⟪finiteFlipHorizonVector F (N + 1), u⟫ = 0 →
          (γ + s) * ‖u‖ ^ 2 ≤ Real.log ((N + 1 : ℕ) : ℝ) * ‖u‖ ^ 2 -
            ⟪Matrix.toEuclideanLin (fullPrimeMatrix (N + 1)) u, u⟫) ↔
        finiteFlipFiniteResolvent F (N + 1) s ≤ 0 := by
  obtain ⟨idx, hAbs, ha⟩ := exists_finiteFlip_conductor_eigenline F hF (by norm_num : 0 < 1)
  have hE := hAbs.sub_const γ
  let t := (s + 2 * Real.log 2) / 2
  have hst : s < t := by dsimp only [t]; linarith only [hs2]
  have ht : 0 < t := hs.trans hst
  have ht2 : t < 2 * Real.log 2 := by dsimp only [t]; linarith only [hs2]
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact (eventually_ge_atTop n).mono fun N hN => by omega
  have hground := hE.eventually_lt_const (by simpa only [ramanujanAdjunctionEnergy_one, sub_self] using hs)
  have hcoord := ha.eventually_const_lt (by
    simpa only [finiteFlipConductorCoefficient,
      (finiteFlipMobius_isMultiplicative F).map_one, Nat.totient_one, Nat.cast_one,
      Real.sqrt_one, mul_one, div_one] using
        sq_pos_of_pos (finiteFlipHarmonicDensity_pos hF))
  filter_upwards [hground, hcoord,
    hshift.eventually (eventually_fullPrime_ground_count_one ht ht2)] with N hg haN hc
  apply finiteFlip_form_iff_resolvent (idx N) hg
  · intro i hi
    have hmem : idx N ∈ fullPrimeEnergySublevel (N + 1) (γ + t) :=
      mem_filter.mpr ⟨mem_univ _, by linarith only [hg, hst]⟩
    have hnot : i ∉ fullPrimeEnergySublevel (N + 1) (γ + t) := fun him =>
      hi ((card_le_one_iff.mp hc.le) him hmem)
    have he : γ + t ≤ fullPrimeEnergyEigenvalue (N + 1) i := by
      apply le_of_not_gt
      intro hlt
      exact hnot (mem_filter.mpr ⟨mem_univ _, hlt⟩)
    linarith only [he, hst]
  · intro hz
    rw [hz] at haN
    norm_num at haN

private theorem gap_downward {ω : ℕ → ℝ} {g h : ℝ}
    (hg : HasHyperplaneGap ω g) (hh : h ≤ g) : HasHyperplaneGap ω h := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hg ε hε
  refine ⟨N₀, fun N hN x hx => (hN₀ N hN x hx).trans ?_⟩
  apply mul_le_mul_of_nonneg_right
  · linarith only [hh]
  · exact sum_nonneg fun n _ => sq_nonneg (x n)

/-- Every finite-prime gap is characterized by the arithmetic secular sign
throughout the interval below it, together with the universal dyadic ceiling. -/
theorem finiteFlip_hasHyperplaneGap_iff_secular (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) (g : ℝ) :
    HasHyperplaneGap (finiteFlip F) g ↔
      g ≤ 2 * Real.log 2 ∧ ∀ s : ℝ, 0 < s → s < g → finiteFlipSecular F s ≤ 0 := by
  constructor
  · intro hg
    have hcap := le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one
      (finiteFlip_mul_self_all F) hg
    refine ⟨hcap, fun s hs hsg => ?_⟩
    have hs2 := hsg.trans_le hcap
    by_contra hnot
    have hpositive := (tendsto_finiteFlipFiniteResolvent F hF hs hs2).eventually_const_lt
      (mul_pos (sq_pos_of_pos (finiteFlipHarmonicDensity_pos hF)) (lt_of_not_ge hnot))
    let ε := (g - s) / 2
    have hε : 0 < ε := by dsimp only [ε]; linarith only [hsg]
    obtain ⟨N₀, hN₀⟩ := hg ε hε
    have hnonpos : ∀ᶠ N : ℕ in atTop, finiteFlipFiniteResolvent F (N + 1) s ≤ 0 := by
      filter_upwards [eventually_finiteFlip_form_iff_resolvent F hF hs hs2,
        eventually_ge_atTop N₀] with N hiff hN
      apply hiff.mp
      apply (finiteFlip_form_bound_iff (by omega : 1 ≤ N + 1) s).mpr
      intro x hx
      apply (hN₀ (N + 1) (by omega) x hx).trans
      apply mul_le_mul_of_nonneg_right
      · dsimp only [ε]
        linarith only [hsg]
      · exact sum_nonneg fun n _ => sq_nonneg (x n)
    obtain ⟨N, hpN, hnN⟩ := (hpositive.and hnonpos).exists
    exact not_lt_of_ge hnN hpN
  · rintro ⟨hcap, hsign⟩
    by_cases hg : 0 < g
    · intro ε hε
      obtain ⟨s, hslo, hsg⟩ := exists_between (max_lt hg (sub_lt_self g hε))
      have hs : 0 < s := (le_max_left 0 (g - ε)).trans_lt hslo
      have hs2 : s < 2 * Real.log 2 := hsg.trans_le hcap
      obtain ⟨t, hst, htg⟩ := exists_between hsg
      have ht : 0 < t := hs.trans hst
      have ht2 : t < 2 * Real.log 2 := htg.trans_le hcap
      have hneg : finiteFlipSecular F s < 0 :=
        (finiteFlipSecular_strictMonoOn F hF ⟨hs, hs2⟩ ⟨ht, ht2⟩ hst).trans_le
          (hsign t ht htg)
      have hnegative := (tendsto_finiteFlipFiniteResolvent F hF hs hs2).eventually_lt_const
        (mul_neg_of_pos_of_neg (sq_pos_of_pos (finiteFlipHarmonicDensity_pos hF)) hneg)
      have hbound : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
          (∑ n ∈ Icc 1 (N + 1), x n / Real.sqrt n) = 0 →
            atomicWeilForm (N + 1) (fun n => finiteFlip F n * x n) ≤
              (Real.log ((N + 1 : ℕ) : ℝ) - γ - s) * ∑ n ∈ Icc 1 (N + 1), x n ^ 2 := by
        filter_upwards [eventually_finiteFlip_form_iff_resolvent F hF hs hs2,
          hnegative] with N hiff hnegN
        exact (finiteFlip_form_bound_iff (by omega : 1 ≤ N + 1) s).mp (hiff.mpr hnegN.le)
      obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hbound
      refine ⟨N₀ + 1, ?_⟩
      intro N hN x hx
      cases N with
      | zero => omega
      | succ N =>
          apply (hN₀ N (by omega) x hx).trans
          apply mul_le_mul_of_nonneg_right
          · have hh := (le_max_right 0 (g - ε)).trans_lt hslo
            linarith only [hh]
          · exact sum_nonneg fun n _ => sq_nonneg (x n)
    · exact gap_downward (hasHyperplaneGap_zero_of_mul_self_eq_one
        (finiteFlip_mul_self_all F)) (le_of_not_gt hg)

/-- The supremum of all uniform finite-prime hyperplane gaps. -/
def finiteFlipGreatestGap (F : Finset ℕ) : ℝ :=
  sSup {g : ℝ | HasHyperplaneGap (finiteFlip F) g}

private theorem finiteFlip_gaps_nonempty (F : Finset ℕ) :
    Set.Nonempty {g : ℝ | HasHyperplaneGap (finiteFlip F) g} :=
  ⟨0, hasHyperplaneGap_zero_of_mul_self_eq_one (finiteFlip_mul_self_all F)⟩

private theorem finiteFlip_gaps_bddAbove (F : Finset ℕ) :
    BddAbove {g : ℝ | HasHyperplaneGap (finiteFlip F) g} :=
  ⟨2 * Real.log 2, fun _ hg =>
    le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one (finiteFlip_mul_self_all F) hg⟩

/-- The secular criterion includes its boundary: the supremum gap is attained. -/
theorem isGreatest_finiteFlip_hyperplaneGap (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    IsGreatest {g : ℝ | HasHyperplaneGap (finiteFlip F) g} (finiteFlipGreatestGap F) := by
  have hcap : finiteFlipGreatestGap F ≤ 2 * Real.log 2 :=
    csSup_le (finiteFlip_gaps_nonempty F) fun g hg =>
      le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one (finiteFlip_mul_self_all F) hg
  refine ⟨(finiteFlip_hasHyperplaneGap_iff_secular F hF _).mpr ⟨hcap, ?_⟩,
    fun g hg => le_csSup (finiteFlip_gaps_bddAbove F) hg⟩
  intro s hs hsg
  have hex : ∃ g : ℝ, HasHyperplaneGap (finiteFlip F) g ∧ s < g := by
    by_contra hnone
    have hupper : ∀ g ∈ {g : ℝ | HasHyperplaneGap (finiteFlip F) g}, g ≤ s := by
      intro g hg
      by_contra hn
      exact hnone ⟨g, hg, lt_of_not_ge hn⟩
    exact not_lt_of_ge (csSup_le (finiteFlip_gaps_nonempty F) hupper) hsg
  obtain ⟨g, hg, hsg'⟩ := hex
  exact ((finiteFlip_hasHyperplaneGap_iff_secular F hF g).mp hg).2 s hs hsg'

/-- Every real gap lies below the attained arithmetic threshold, and every
smaller value is itself a uniform gap. -/
theorem finiteFlip_hasHyperplaneGap_iff_le_greatestGap (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) (g : ℝ) :
    HasHyperplaneGap (finiteFlip F) g ↔ g ≤ finiteFlipGreatestGap F :=
  ⟨fun hg => (isGreatest_finiteFlip_hyperplaneGap F hF).2 hg,
    fun hg => gap_downward (isGreatest_finiteFlip_hyperplaneGap F hF).1 hg⟩

/-- The exact greatest gap retains the counted density bound and never exceeds
the first global excitation. -/
theorem finiteFlipGreatestGap_bounds (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    2 * Real.log 2 * finiteFlipHarmonicDensity F ^ 2 ≤ finiteFlipGreatestGap F ∧
      finiteFlipGreatestGap F ≤ 2 * Real.log 2 :=
  ⟨(isGreatest_finiteFlip_hyperplaneGap F hF).2 (finiteFlip_hasHyperplaneGap hF),
    le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one (finiteFlip_mul_self_all F)
      (isGreatest_finiteFlip_hyperplaneGap F hF).1⟩

/-- Every fixed finite prime set has a strictly positive attained greatest gap. -/
theorem finiteFlipGreatestGap_pos (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    0 < finiteFlipGreatestGap F :=
  (mul_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
    (sq_pos_of_pos (finiteFlipHarmonicDensity_pos hF))).trans_le
      (finiteFlipGreatestGap_bounds F hF).1

/-- Enlarging the flipped-prime set can only add supported conductor weight. -/
theorem finiteFlipSpectralWeight_mono {F G : Finset ℕ} (hFG : F ⊆ G) (m : ℕ) :
    finiteFlipSpectralWeight F m ≤ finiteFlipSpectralWeight G m := by
  classical
  rw [finiteFlipSpectralWeight_eq, finiteFlipSpectralWeight_eq]
  by_cases hmF : m ∈ Nat.factoredNumbers F
  · have hmG : m ∈ Nat.factoredNumbers G :=
      ⟨hmF.1, fun p hp => hFG (hmF.2 p hp)⟩
    rw [if_pos hmF, if_pos hmG]
  · rw [if_neg hmF]
    split_ifs
    · positivity
    · exact le_refl _

/-- At every energy below the first excitation, adding flipped primes increases
the normalized secular function. -/
theorem finiteFlipSecular_mono {F G : Finset ℕ} (hFG : F ⊆ G)
    (hG : ∀ p ∈ G, p.Prime) {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    finiteFlipSecular F s ≤ finiteFlipSecular G s := by
  have hF : ∀ p ∈ F, p.Prime := fun p hp => hG p (hFG hp)
  unfold finiteFlipSecular
  apply add_le_add le_rfl
  apply Summable.tsum_mono (summable_finiteFlipSecularTail F hF hs hs2)
    (summable_finiteFlipSecularTail G hG hs hs2)
  intro k
  have henergy := (ramanujanAdjunctionEnergy_sub_one_ge (by omega : 2 ≤ k + 2)).1
  rw [ramanujanAdjunctionEnergy_one] at henergy
  exact div_le_div_of_nonneg_right (finiteFlipSpectralWeight_mono hFG _)
    (sub_pos.mpr (hs2.trans_le henergy)).le

/-- Joint flips decrease the exact attained gap under inclusion of prime sets. -/
theorem finiteFlipGreatestGap_antitone {F G : Finset ℕ} (hFG : F ⊆ G)
    (hG : ∀ p ∈ G, p.Prime) : finiteFlipGreatestGap G ≤ finiteFlipGreatestGap F := by
  have hF : ∀ p ∈ F, p.Prime := fun p hp => hG p (hFG hp)
  apply (isGreatest_finiteFlip_hyperplaneGap F hF).2
  apply (finiteFlip_hasHyperplaneGap_iff_secular F hF _).mpr
  have hchar := (finiteFlip_hasHyperplaneGap_iff_secular G hG _).mp
    (isGreatest_finiteFlip_hyperplaneGap G hG).1
  refine ⟨hchar.1, fun s hs hsg => ?_⟩
  exact (finiteFlipSecular_mono hFG hG hs (hsg.trans_le hchar.1)).trans (hchar.2 s hs hsg)

end GaloisForLFunctions.ArithmeticCountingPositivity
