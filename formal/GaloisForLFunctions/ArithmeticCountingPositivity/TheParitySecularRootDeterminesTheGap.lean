import GaloisForLFunctions.ArithmeticCountingPositivity.TheParityTowerDeterminesTheFiniteResolvent
import GaloisForLFunctions.ArithmeticCountingPositivity.SmallPrimeFlipsLieBelowTheMaximalGap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonLawsHoldForProfilesOfBoundedVariation

/-!
# The parity secular root determines the exact hyperplane gap

The full finite resolvent detects the constrained prime form between its
first two energies. Its arithmetic limit identifies the greatest parity
gap as the smaller of the secular root and the first global excitation.
For primes below eleven this is exactly the secular root.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

private theorem parity_mean_pos {p : ℕ} (hp : p.Prime) : 0 < primeParityMean p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact div_pos (sub_pos.mpr hpR) (by positivity)

private theorem parity_harmonic_sum {N : ℕ} (hN : 1 ≤ N) (p : ℕ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    (∑ k : PrimeHorizonIndex N, finiteFlip {p} k * u k / Real.sqrt k) =
      Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) * ⟪primeParityHorizonVector p N, u⟫ := by
  have hS : 0 < Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) :=
    Real.sqrt_pos.mpr (gaugeHarmonicSum_one_pos hN)
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ k : PrimeHorizonIndex N, finiteFlip {p} k * u k / Real.sqrt k) =
    Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) *
      ∑ k : PrimeHorizonIndex N,
        u k * (finiteFlip {p} k / Real.sqrt k /
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
orthogonal complement of the normalized parity vector. -/
private theorem parity_form_bound_iff {p N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    (∀ u : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪primeParityHorizonVector p N, u⟫ = 0 →
      (γ + s) * ‖u‖ ^ 2 ≤ Real.log N * ‖u‖ ^ 2 -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) ↔
      (∀ x : ℕ → ℝ, (∑ n ∈ Icc 1 N, x n / Real.sqrt n) = 0 →
        atomicWeilForm N (fun n => finiteFlip {p} n * x n) ≤
          (Real.log N - γ - s) * ∑ n ∈ Icc 1 N, x n ^ 2) := by
  constructor
  · intro h x hx
    let u : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
      WithLp.toLp 2 (fun i => finiteFlip {p} i * x i)
    have hu : ⟪primeParityHorizonVector p N, u⟫ = 0 := by
      have hS := (Real.sqrt_pos.mpr (gaugeHarmonicSum_one_pos hN)).ne'
      apply (mul_eq_zero.mp (show Real.sqrt (gaugeHarmonicSum (fun _ => 1) N) *
        ⟪primeParityHorizonVector p N, u⟫ = 0 from ?_)).resolve_left hS
      rw [← parity_harmonic_sum hN p u]
      change (∑ i : PrimeHorizonIndex N, finiteFlip {p} i * (finiteFlip {p} i * x i) /
        Real.sqrt i) = 0
      simp_rw [← mul_assoc, singleFlip_mul_self, one_mul]
      exact (sum_coe_sort (Icc 1 N) (fun n => x n / Real.sqrt n)).trans hx
    have hmass : ‖u‖ ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change (∑ i : PrimeHorizonIndex N, (finiteFlip {p} i * x i) ^ 2) = _
      simp_rw [mul_pow, sq (finiteFlip {p} _), singleFlip_mul_self, one_mul]
      exact sum_coe_sort (Icc 1 N) (fun n => x n ^ 2)
    have hform : atomicWeilForm N (fun n => finiteFlip {p} n * x n) =
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
    let x : ℕ → ℝ := fun n => finiteFlip {p} n * horizonExtend ⇑u n
    have hx : (∑ n ∈ Icc 1 N, x n / Real.sqrt n) = 0 := by
      change (∑ n ∈ Icc 1 N, finiteFlip {p} n * horizonExtend ⇑u n / Real.sqrt n) = 0
      rw [sum_horizonExtend ⇑u (fun n t => finiteFlip {p} n * t / Real.sqrt n),
        parity_harmonic_sum hN p u, hu, mul_zero]
    have hmass : (∑ n ∈ Icc 1 N, x n ^ 2) = ‖u‖ ^ 2 := by
      calc
        _ = ∑ n ∈ Icc 1 N, horizonExtend ⇑u n ^ 2 := by
          refine sum_congr rfl fun n _ => ?_
          dsimp only [x]
          rw [mul_pow, sq (finiteFlip {p} n), singleFlip_mul_self, one_mul]
        _ = ∑ i : PrimeHorizonIndex N, u i ^ 2 := sum_horizonExtend ⇑u (fun _ t => t ^ 2)
        _ = _ := (EuclideanSpace.real_norm_sq_eq u).symm
    have htwist : (fun n => finiteFlip {p} n * x n) = horizonExtend ⇑u := by
      funext n
      dsimp only [x]
      rw [← mul_assoc, singleFlip_mul_self, one_mul]
    have hb := h x hx
    rw [htwist, atomicWeilForm_horizonExtend, prime_quadratic_eq_inner, hmass] at hb
    nlinarith only [hb]

private theorem parity_form_iff_resolvent {p N : ℕ} {s : ℝ}
    (i₀ : PrimeHorizonIndex N)
    (hneg : fullPrimeEnergyEigenvalue N i₀ - γ < s)
    (hpos : ∀ i, i ≠ i₀ → s < fullPrimeEnergyEigenvalue N i - γ)
    (hv : ⟪primeParityHorizonVector p N,
      (fullPrimeMatrix_isHermitian N).eigenvectorBasis i₀⟫ ≠ 0) :
    (∀ u : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪primeParityHorizonVector p N, u⟫ = 0 →
      (γ + s) * ‖u‖ ^ 2 ≤ Real.log N * ‖u‖ ^ 2 -
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫) ↔
      primeParityFiniteResolvent p N s ≤ 0 := by
  let a : PrimeHorizonIndex N → ℝ := fun i =>
    ⟪primeParityHorizonVector p N, (fullPrimeMatrix_isHermitian N).eigenvectorBasis i⟫
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
    (primeParityHorizonVector p N) (Real.log N) (γ + s) i₀ hn hp' hv
  have hd (i : PrimeHorizonIndex N) : Real.log N - (fullPrimeMatrix_isHermitian N).eigenvalues i -
      (γ + s) = fullPrimeEnergyEigenvalue N i - γ - s := by
    rw [fullPrimeEnergyEigenvalue]
    ring
  simp only [hd] at he
  rw [he]
  change b * S ≤ a i₀ ^ 2 ↔ primeParityFiniteResolvent p N s ≤ 0
  have hhead : fullPrimeEnergyEigenvalue N i₀ - γ - s = -b := by dsimp only [b]; ring
  have hsplit : primeParityFiniteResolvent p N s = a i₀ ^ 2 / (-b) + S := by
    rw [primeParityFiniteResolvent, ← sum_erase_add _ _ (mem_univ i₀), hhead]
    change S + a i₀ ^ 2 / (-b) = a i₀ ^ 2 / (-b) + S
    ring
  have hscale : b * primeParityFiniteResolvent p N s = b * S - a i₀ ^ 2 := by
    rw [hsplit]
    field_simp [hb.ne']
    ring
  constructor
  · intro hpaid
    have hh : b * primeParityFiniteResolvent p N s ≤ b * 0 := by
      rw [hscale, mul_zero]
      linarith only [hpaid]
    exact le_of_mul_le_mul_left hh hb
  · intro hF
    have hh := mul_nonpos_of_nonneg_of_nonpos hb.le hF
    rw [hscale] at hh
    linarith only [hh]

private theorem eventually_parity_form_iff_resolvent {p : ℕ} (hp : p.Prime) {s : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    ∀ᶠ N : ℕ in atTop,
      (∀ u : EuclideanSpace ℝ (PrimeHorizonIndex (N + 1)),
        ⟪primeParityHorizonVector p (N + 1), u⟫ = 0 →
          (γ + s) * ‖u‖ ^ 2 ≤ Real.log ((N + 1 : ℕ) : ℝ) * ‖u‖ ^ 2 -
            ⟪Matrix.toEuclideanLin (fullPrimeMatrix (N + 1)) u, u⟫) ↔
        primeParityFiniteResolvent p (N + 1) s ≤ 0 := by
  obtain ⟨idx, hE, ha⟩ := exists_primeParity_tower_eigenline hp 0
  let t := (s + 2 * Real.log 2) / 2
  have hst : s < t := by dsimp only [t]; linarith only [hs2]
  have ht : 0 < t := hs.trans hst
  have ht2 : t < 2 * Real.log 2 := by dsimp only [t]; linarith only [hs2]
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact (eventually_ge_atTop n).mono fun N hN => by omega
  have hground := hE.eventually_lt_const (by simpa only [primeParityTowerEnergy] using hs)
  have hcoord := ha.eventually_const_lt (by
    simpa only [primeParityTowerCoefficient] using sq_pos_of_pos (parity_mean_pos hp))
  filter_upwards [hground, hcoord,
    hshift.eventually (eventually_fullPrime_ground_count_one ht ht2)] with N hg haN hc
  apply parity_form_iff_resolvent (idx N) hg
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

private theorem parity_secular_strictMono {p : ℕ} (hp : p.Prime) :
    StrictMonoOn (RHTower.infiniteSecular (primeParityTowerEnergy p) (primeParityTowerCoefficient p))
      (Set.Ioo 0 (primeParityTowerEnergy p 1)) := by
  have hD := primeParityTowerEnergy_strictMono hp
  have h0 : primeParityTowerCoefficient p 0 ≠ 0 := (parity_mean_pos hp).ne'
  exact RHTower.infiniteSecular_strictMonoOn (hD (by omega : 1 < 2))
    (fun j => hD.monotone (by omega)) (hasSum_primeParityTowerCoefficient_sq hp).summable h0

private theorem parity_secular_neg {p : ℕ} (hp : p.Prime) {s : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * Real.log 2) (hsroot : s < primeParitySecularRoot p) :
    RHTower.infiniteSecular (primeParityTowerEnergy p) (primeParityTowerCoefficient p) s < 0 := by
  obtain ⟨hr, hz, hr1⟩ := primeParitySecularRoot_spec hp
  have hs1 : s < primeParityTowerEnergy p 1 := hs2.trans_le (primeParityTowerEnergy_ge_excitation hp 0)
  have h := parity_secular_strictMono hp ⟨hs, hs1⟩ ⟨hr.1, hr1⟩ hsroot
  rwa [hz] at h

private theorem parity_secular_pos {p : ℕ} (hp : p.Prime) {s : ℝ}
    (hs : 0 < s) (hs2 : s < 2 * Real.log 2) (hsroot : primeParitySecularRoot p < s) :
    0 < RHTower.infiniteSecular (primeParityTowerEnergy p) (primeParityTowerCoefficient p) s := by
  obtain ⟨hr, hz, hr1⟩ := primeParitySecularRoot_spec hp
  have hs1 : s < primeParityTowerEnergy p 1 := hs2.trans_le (primeParityTowerEnergy_ge_excitation hp 0)
  have h := parity_secular_strictMono hp ⟨hr.1, hr1⟩ ⟨hs, hs1⟩ hsroot
  rwa [hz] at h

/-- The smaller of the arithmetic secular root and the first global excitation
is attained as a uniform hyperplane gap, including its endpoint. -/
theorem primeFlip_hasHyperplaneGap_min_secularRoot {p : ℕ} (hp : p.Prime) :
    HasHyperplaneGap (finiteFlip {p}) (min (2 * Real.log 2) (primeParitySecularRoot p)) := by
  let δ := min (2 * Real.log 2) (primeParitySecularRoot p)
  have hδ : 0 < δ := lt_min (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
    (primeParitySecularRoot_spec hp).1.1
  intro ε hε
  obtain ⟨s, hslo, hshi⟩ := exists_between (max_lt hδ (sub_lt_self δ hε))
  have hs : 0 < s := (le_max_left 0 (δ - ε)).trans_lt hslo
  have hs2 : s < 2 * Real.log 2 := hshi.trans_le (min_le_left _ _)
  have hsroot : s < primeParitySecularRoot p := hshi.trans_le (min_le_right _ _)
  have hnegative := (tendsto_primeParityFiniteResolvent hp hs hs2).eventually_lt_const
    (parity_secular_neg hp hs hs2 hsroot)
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      (∑ n ∈ Icc 1 (N + 1), x n / Real.sqrt n) = 0 →
        atomicWeilForm (N + 1) (fun n => finiteFlip {p} n * x n) ≤
          (Real.log ((N + 1 : ℕ) : ℝ) - γ - s) * ∑ n ∈ Icc 1 (N + 1), x n ^ 2 := by
    filter_upwards [eventually_parity_form_iff_resolvent hp hs hs2, hnegative] with N hiff hneg
    exact (parity_form_bound_iff (by omega : 1 ≤ N + 1) s).mp (hiff.mpr hneg.le)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hbound
  refine ⟨N₀ + 1, ?_⟩
  intro N hN x hx
  cases N with
  | zero => omega
  | succ N =>
      have hb := hN₀ N (by omega) x hx
      apply hb.trans
      apply mul_le_mul_of_nonneg_right
      · have hh := (le_max_right 0 (δ - ε)).trans_lt hslo
        change Real.log ((N + 1 : ℕ) : ℝ) - γ - s ≤ Real.log ((N + 1 : ℕ) : ℝ) - γ - δ + ε
        linarith only [hh]
      · exact sum_nonneg fun n _ => sq_nonneg (x n)

/-- Every prime-parity hyperplane gap is bounded by the full arithmetic secular root. -/
theorem primeFlip_hyperplaneGap_le_secularRoot {p : ℕ} (hp : p.Prime) {g : ℝ}
    (hg : HasHyperplaneGap (finiteFlip {p}) g) : g ≤ primeParitySecularRoot p := by
  by_contra hnot
  have hrootg : primeParitySecularRoot p < g := lt_of_not_ge hnot
  obtain ⟨s, hroots, hsg⟩ := exists_between hrootg
  have hs : 0 < s := (primeParitySecularRoot_spec hp).1.1.trans hroots
  have hsglobal := le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one (singleFlip_mul_self p) hg
  have hs2 : s < 2 * Real.log 2 := hsg.trans_le hsglobal
  have hpositive := (tendsto_primeParityFiniteResolvent hp hs hs2).eventually_const_lt
    (parity_secular_pos hp hs hs2 hroots)
  let ε := (g - s) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith only [hsg]
  obtain ⟨N₀, hN₀⟩ := hg ε hε
  have hnonpos : ∀ᶠ N : ℕ in atTop, primeParityFiniteResolvent p (N + 1) s ≤ 0 := by
    filter_upwards [eventually_parity_form_iff_resolvent hp hs hs2,
      eventually_ge_atTop N₀] with N hiff hN
    apply hiff.mp
    apply (parity_form_bound_iff (by omega : 1 ≤ N + 1) s).mpr
    intro x hx
    apply (hN₀ (N + 1) (by omega) x hx).trans
    apply mul_le_mul_of_nonneg_right
    · dsimp only [ε]
      linarith only [hsg]
    · exact sum_nonneg fun n _ => sq_nonneg (x n)
  obtain ⟨N, hpN, hnN⟩ := (hpositive.and hnonpos).exists
  exact not_lt_of_ge hnN hpN

/-- The exact greatest single-prime gap is the minimum of the secular root
and the universal dyadic ceiling. -/
theorem isGreatest_primeFlip_hyperplaneGap_min_secularRoot {p : ℕ} (hp : p.Prime) :
    IsGreatest {g | HasHyperplaneGap (finiteFlip {p}) g}
      (min (2 * Real.log 2) (primeParitySecularRoot p)) := by
  refine ⟨primeFlip_hasHyperplaneGap_min_secularRoot hp, fun g hg => ?_⟩
  exact le_min
    (le_two_mul_log_two_of_hasHyperplaneGap_of_mul_self_eq_one (singleFlip_mul_self p) hg)
    (primeFlip_hyperplaneGap_le_secularRoot hp hg)

/-- Every real gap value is classified by the exact arithmetic spectral threshold. -/
theorem primeFlip_hasHyperplaneGap_iff_le_min_secularRoot {p : ℕ} (hp : p.Prime) (g : ℝ) :
    HasHyperplaneGap (finiteFlip {p}) g ↔
      g ≤ min (2 * Real.log 2) (primeParitySecularRoot p) := by
  constructor
  · intro hg
    exact (isGreatest_primeFlip_hyperplaneGap_min_secularRoot hp).2 hg
  · intro hle ε hε
    obtain ⟨N₀, hN₀⟩ := primeFlip_hasHyperplaneGap_min_secularRoot hp ε hε
    refine ⟨N₀, fun N hN x hx => (hN₀ N hN x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right
    · linarith only [hle]
    · exact sum_nonneg fun n _ => sq_nonneg (x n)

/-- The arithmetic root lies below the dyadic ceiling exactly at primes below eleven. -/
theorem primeParitySecularRoot_lt_two_mul_log_two_iff {p : ℕ} (hp : p.Prime) :
    primeParitySecularRoot p < 2 * Real.log 2 ↔ p < 11 := by
  constructor
  · intro hroot
    by_contra hnot
    have hgap := (primeFlip_hasHyperplaneGap_two_mul_log_two_iff hp).mpr (le_of_not_gt hnot)
    exact not_lt_of_ge (primeFlip_hyperplaneGap_le_secularRoot hp hgap) hroot
  · intro hpSmall
    by_contra hnot
    have hmin : min (2 * Real.log 2) (primeParitySecularRoot p) = 2 * Real.log 2 :=
      min_eq_left (le_of_not_gt hnot)
    have hgap := primeFlip_hasHyperplaneGap_min_secularRoot hp
    rw [hmin] at hgap
    exact (Nat.not_le_of_gt hpSmall) ((primeFlip_hasHyperplaneGap_two_mul_log_two_iff hp).mp hgap)

/-- At every prime below eleven, the unique arithmetic secular root is the greatest gap. -/
theorem isGreatest_smallPrimeFlip_hyperplaneGap_secularRoot {p : ℕ}
    (hp : p.Prime) (hpSmall : p < 11) :
    IsGreatest {g | HasHyperplaneGap (finiteFlip {p}) g} (primeParitySecularRoot p) := by
  have hroot := (primeParitySecularRoot_lt_two_mul_log_two_iff hp).mpr hpSmall
  simpa only [min_eq_right hroot.le] using isGreatest_primeFlip_hyperplaneGap_min_secularRoot hp

/-- The full parity tower makes the two-mode upper bound strict for every prime. -/
theorem primeFlip_hyperplaneGap_lt_prime_log_div {p : ℕ} (hp : p.Prime) {g : ℝ}
    (hg : HasHyperplaneGap (finiteFlip {p}) g) :
    g < (p : ℝ) * Real.log p / ((p : ℝ) + 3) :=
  (primeFlip_hyperplaneGap_le_secularRoot hp hg).trans_lt (primeParitySecularRoot_spec hp).1.2

/-- The exact root satisfies the explicit normalized series with no coefficient
normalization factor: its positive reciprocal tail sums to its reciprocal. -/
theorem hasSum_primeParitySecularRoot_reciprocals {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => 4 /
      (((p ^ (k + 1)).totient : ℝ) *
        (primeParityTowerEnergy p (k + 1) - primeParitySecularRoot p)))
      (1 / primeParitySecularRoot p) := by
  obtain ⟨hr, hz, hr1⟩ := primeParitySecularRoot_spec hp
  have hD := primeParityTowerEnergy_strictMono hp
  have hsum2 := RHTower.summable_infiniteSecularTail
    (fun j => hD.monotone (by omega : 2 ≤ j + 2))
    (hasSum_primeParityTowerCoefficient_sq hp).summable
    (hr1.trans (hD (by omega : 1 < 2)))
  have hfull : Summable (fun k : ℕ => primeParityTowerCoefficient p k ^ 2 /
      (primeParityTowerEnergy p k - primeParitySecularRoot p)) :=
    (summable_nat_add_iff 2).mp hsum2
  have htail := (summable_nat_add_iff 1).mpr hfull
  have hzero : (∑' k : ℕ, primeParityTowerCoefficient p k ^ 2 /
      (primeParityTowerEnergy p k - primeParitySecularRoot p)) = 0 := by
    rw [← RHTower.infiniteSecular_eq_tsum hfull]
    exact hz
  rw [hfull.tsum_eq_zero_add] at hzero
  change primeParityMean p ^ 2 / (0 - primeParitySecularRoot p) +
    (∑' k : ℕ, primeParityTowerCoefficient p (k + 1) ^ 2 /
      (primeParityTowerEnergy p (k + 1) - primeParitySecularRoot p)) = 0 at hzero
  rw [zero_sub, div_neg] at hzero
  have hvalue : (∑' k : ℕ, primeParityTowerCoefficient p (k + 1) ^ 2 /
      (primeParityTowerEnergy p (k + 1) - primeParitySecularRoot p)) =
        primeParityMean p ^ 2 / primeParitySecularRoot p := by linarith only [hzero]
  have hc : primeParityMean p ≠ 0 := (parity_mean_pos hp).ne'
  have hseries := htail.hasSum.mul_left (1 / primeParityMean p ^ 2)
  have he : (fun k : ℕ => (1 / primeParityMean p ^ 2) *
      (primeParityTowerCoefficient p (k + 1) ^ 2 /
        (primeParityTowerEnergy p (k + 1) - primeParitySecularRoot p))) =
      (fun k : ℕ => 4 / (((p ^ (k + 1)).totient : ℝ) *
        (primeParityTowerEnergy p (k + 1) - primeParitySecularRoot p))) := by
    funext k
    have hsq : primeParityTowerCoefficient p (k + 1) ^ 2 =
        4 * primeParityMean p ^ 2 / ((p ^ (k + 1)).totient : ℝ) := by
      rw [Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_sub hp.one_le, Nat.cast_one]
      exact primeParityTowerCoefficient_sq_succ hp k
    have hphi : (0 : ℝ) < (p ^ (k + 1)).totient := by
      exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos (k + 1))
    have hden : 0 < primeParityTowerEnergy p (k + 1) - primeParitySecularRoot p :=
      sub_pos.mpr (hr1.trans_le (hD.monotone (by omega : 1 ≤ k + 1)))
    rw [hsq]
    field_simp [hc, hphi.ne', hden.ne']
  have hcanc : (1 / primeParityMean p ^ 2) *
      (primeParityMean p ^ 2 / primeParitySecularRoot p) = 1 / primeParitySecularRoot p := by
    field_simp [hc, hr.1.ne']
  rw [he, hvalue, hcanc] at hseries
  exact hseries

end GaloisForLFunctions.ArithmeticCountingPositivity
