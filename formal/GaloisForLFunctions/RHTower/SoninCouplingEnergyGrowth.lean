import GaloisForLFunctions.RHTower.SoninSubAnnulusCouplingLimit
import GaloisForLFunctions.RHTower.SoninPacketDisjointOrthogonality
import GaloisForLFunctions.HTGeometry.HilbertSchmidtDominatesPointwise
import GaloisForLFunctions.RHTower.SoninCompletionSummabilityCriterion

/-!
# Many disjoint annuli force large coupling energy

Packets on disjoint sub-annuli of the aperture window are orthogonal, and the coupling carries each
of them to its own dilate without losing norm in the limit.  Normalising them gives an orthonormal
family that the coupling asymptotically preserves, and the Hilbert--Schmidt energy dominates the
total image energy of any orthonormal family.

So a window cut into `N` annuli forces the coupling energy above `N - 1` at every large scale.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- **Energy from a disjoint annulus family.**  With `N` pairwise disjoint annuli inside the
aperture window, the coupling energy eventually exceeds `N - 1`. -/
theorem eventually_sub_one_le_hsNormSq_of_disjointAnnuli
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (N : ℕ) (β γ : Fin N → ℝ) (hβ : ∀ j, 0 < β j) (hβγ : ∀ j, β j < γ j)
    (hbβ : ∀ j, b ≤ β j) (hγc : ∀ j, γ j ≤ c)
    (hdisj : ∀ j k : Fin N, j < k → γ j ≤ β k)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c < r n * a)
    (hr : Tendsto r atTop atTop) :
    ∀ᶠ n : ℕ in atTop, (N : ℝ) - 1 ≤ hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)) := by
  classical
  set κ : ℕ → ℝ := fun n => 2 * Real.pi * (r n * q) with hκ
  set w : Fin N → ℕ → evenSubspace :=
    fun j n => soninPacketEven (β j) (γ j) (hβ j) (hβγ j) (κ n) with hw
  set L : Fin N → ℝ :=
    fun j => Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump (β j) (γ j) (hβγ j) x ^ 2) with hL
  have hLpos : ∀ j, 0 < L j := fun j => sqrt_half_energy_pos (β j) (γ j) (hβ j) (hβγ j)
  have hfreq : Tendsto κ atTop atTop := by
    have hq : 0 < q := ha.trans haq
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  -- the packet norms and the coupled norms both settle at the same positive value
  have hnorm : ∀ j, Tendsto (fun n => ‖w j n‖) atTop (𝓝 (L j)) := fun j =>
    tendsto_norm_soninPacketEven (β j) (γ j) (hβ j) (hβγ j) κ hfreq
  have hcoupled : ∀ j, Tendsto (fun n =>
      ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) (w j n)‖) atTop
      (𝓝 (L j)) := fun j =>
    tendsto_norm_soninApertureCoupling_apply_soninPacketEven_subAnnulus a b c (β j) (γ j)
      ha hb hab hbc (hβ j) (hβγ j) (hbβ j) (hγc j) q haq hqb r hrpos hrgt
      (fun n => (hcr n).le) hr
  -- the normalised ratios tend to one
  have hratio : ∀ j, Tendsto (fun n =>
      (‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) (w j n)‖ /
        ‖w j n‖) ^ 2) atTop (𝓝 1) := by
    intro j
    have hdiv : Tendsto (fun n =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) (w j n)‖ /
          ‖w j n‖) atTop (𝓝 (L j / L j)) :=
      (hcoupled j).div (hnorm j) (hLpos j).ne'
    rw [div_self (hLpos j).ne'] at hdiv
    simpa using hdiv.pow 2
  have hsum : Tendsto (fun n => ∑ j : Fin N,
      (‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) (w j n)‖ /
        ‖w j n‖) ^ 2) atTop (𝓝 (N : ℝ)) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin N))
      (fun j _ => hratio j)
    simpa using h
  have hne : ∀ j, ∀ᶠ n : ℕ in atTop, ‖w j n‖ ≠ 0 := by
    intro j
    have hhalf : L j / 2 < L j := by linarith [hLpos j]
    filter_upwards [(hnorm j).eventually_const_lt hhalf] with n hn
    have hpos : 0 < ‖w j n‖ := lt_trans (half_pos (hLpos j)) hn
    exact hpos.ne'
  have hall : ∀ᶠ n : ℕ in atTop, ∀ j, ‖w j n‖ ≠ 0 := Filter.eventually_all.mpr hne
  have hbig : ∀ᶠ n : ℕ in atTop, (N : ℝ) - 1 < ∑ j : Fin N,
      (‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) (w j n)‖ /
        ‖w j n‖) ^ 2 :=
    hsum.eventually_const_lt (by linarith)
  filter_upwards [hall, hbig] with n hnz hgt
  -- the normalised packets form an orthonormal family
  set e : Fin N → evenSubspace :=
    fun j => ((‖w j n‖ : ℝ) : ℂ)⁻¹ • w j n with he
  have hzero : ∀ j k : Fin N, j ≠ k → ⟪w j n, w k n⟫_ℂ = 0 := by
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with hlt | hgt'
    · exact inner_soninPacketEven_eq_zero_of_disjoint (β j) (γ j) (β k) (γ k) (hβ j) (hβγ j)
        (hβ k) (hβγ k) (hdisj j k hlt) (κ n) (κ n)
    · exact inner_soninPacketEven_eq_zero_of_disjoint' (β k) (γ k) (β j) (γ j) (hβ k) (hβγ k)
        (hβ j) (hβγ j) (hdisj k j hgt') (κ n) (κ n)
  have hortho : Orthonormal ℂ e := by
    constructor
    · intro j
      have hpos : 0 < ‖w j n‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hnz j))
      show ‖((‖w j n‖ : ℝ) : ℂ)⁻¹ • w j n‖ = 1
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
        inv_mul_cancel₀ hpos.ne']
    · intro j k hjk
      show ⟪((‖w j n‖ : ℝ) : ℂ)⁻¹ • w j n, ((‖w k n‖ : ℝ) : ℂ)⁻¹ • w k n⟫_ℂ = 0
      rw [inner_smul_left (𝕜 := ℂ) (w j n) (((‖w k n‖ : ℝ) : ℂ)⁻¹ • w k n),
        inner_smul_right (𝕜 := ℂ) (w j n) (w k n), hzero j k hjk, mul_zero, mul_zero]
  have hHS : (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)).IsHilbertSchmidt :=
    evenSoninApertureSuccessiveLayerTransition_isHilbertSchmidt ha hab hbc (hrgt n) (hcr n)
  have hdom := sum_norm_sq_apply_le_hsNormSq hHS hortho
  have hterm : ∀ j : Fin N,
      ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) (e j)‖ ^ 2 =
      (‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) (w j n)‖ /
        ‖w j n‖) ^ 2 := by
    intro j
    have hpos : 0 < ‖w j n‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hnz j))
    show ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
        (((‖w j n‖ : ℝ) : ℂ)⁻¹ • w j n)‖ ^ 2 =
      (‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) (w j n)‖ /
        ‖w j n‖) ^ 2
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
      div_eq_inv_mul]
  rw [Finset.sum_congr rfl fun j _ => hterm j] at hdom
  linarith

/-- The uniform subdivision of the aperture window into `N` annuli. -/
def soninUniformAnnulusFloor (b c : ℝ) (N : ℕ) (j : ℕ) : ℝ := b + j * ((c - b) / N)

/-- **A window cut into `N` disjoint annuli.** -/
theorem exists_disjoint_annulus_family (b c : ℝ) (hb : 0 < b) (hbc : b < c) (N : ℕ) :
    ∃ β γ : Fin N → ℝ, (∀ j, 0 < β j) ∧ (∀ j, β j < γ j) ∧ (∀ j, b ≤ β j) ∧
      (∀ j, γ j ≤ c) ∧ ∀ j k : Fin N, j < k → γ j ≤ β k := by
  refine ⟨fun j => soninUniformAnnulusFloor b c N j,
    fun j => soninUniformAnnulusFloor b c N (j + 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have hd : 0 ≤ (c - b) / N := div_nonneg (by linarith) (Nat.cast_nonneg N)
    have : 0 ≤ (j : ℝ) * ((c - b) / N) := mul_nonneg (Nat.cast_nonneg _) hd
    simp only [soninUniformAnnulusFloor]
    linarith
  · intro j
    have hNpos : (0 : ℝ) < N := by exact_mod_cast j.pos
    have hd : 0 < (c - b) / N := div_pos (by linarith) hNpos
    have hstep : ((j : ℕ) : ℝ) * ((c - b) / N) < (((j : ℕ) + 1 : ℕ) : ℝ) * ((c - b) / N) := by
      have : ((j : ℕ) : ℝ) < (((j : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self _
      exact mul_lt_mul_of_pos_right this hd
    simp only [soninUniformAnnulusFloor]
    linarith
  · intro j
    have hd : 0 ≤ (c - b) / N := div_nonneg (by linarith) (Nat.cast_nonneg N)
    have : 0 ≤ (j : ℝ) * ((c - b) / N) := mul_nonneg (Nat.cast_nonneg _) hd
    simp only [soninUniformAnnulusFloor]
    linarith
  · intro j
    have hNpos : (0 : ℝ) < N := by exact_mod_cast j.pos
    have hd : 0 < (c - b) / N := div_pos (by linarith) hNpos
    have hle : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast j.isLt
    have hmul : (((j : ℕ) + 1 : ℕ) : ℝ) * ((c - b) / N) ≤ (N : ℝ) * ((c - b) / N) :=
      mul_le_mul_of_nonneg_right hle hd.le
    have hcancel : (N : ℝ) * ((c - b) / N) = c - b := by
      field_simp
    simp only [soninUniformAnnulusFloor]
    linarith
  · intro j k hjk
    have hd : 0 ≤ (c - b) / N := div_nonneg (by linarith) (Nat.cast_nonneg N)
    have hle : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hjk
    have := mul_le_mul_of_nonneg_right hle hd
    simp only [soninUniformAnnulusFloor]
    linarith

/-- **The coupling energy grows without bound.**  For every strict aperture flag the successive
layer coupling has Hilbert--Schmidt energy tending to infinity along any clock past the crossing
threshold. -/
theorem tendsto_hsNormSq_soninApertureCoupling_atTop
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c < r n * a)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n => hsNormSq
      (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))) atTop atTop := by
  refine tendsto_atTop.mpr fun M => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (M + 1)
  obtain ⟨β, γ, h1, h2, h3, h4, h5⟩ := exists_disjoint_annulus_family b c hb hbc N
  filter_upwards [eventually_sub_one_le_hsNormSq_of_disjointAnnuli a b c ha hb hab hbc q haq hqb
    N β γ h1 h2 h3 h4 h5 r hrpos hrgt hcr hr] with n hn
  linarith

/-- **No completion bounded above can restore the floor.**  Along the crossing clock the coupling
energy is unbounded, so every completion that stays bounded above on the scales leaves the packet
channel unbounded below. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_bddAbove
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (κ : ℕ → ℝ) (M₀ : ℝ) (hκ : ∀ i, κ i ≤ M₀) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c) κ :=
  not_bddBelow_of_tendsto_hsNormSq_atTop ha hab hbc (soninCrossingClock a c)
    (one_lt_soninCrossingClock a c) (fun i => lt_soninCrossingClock_mul a c ha i) κ M₀ hκ
    (tendsto_hsNormSq_soninApertureCoupling_atTop a b c ha hb hab hbc q haq hqb
      (soninCrossingClock a c) (soninCrossingClock_pos a c) (one_lt_soninCrossingClock a c)
      (fun n => lt_soninCrossingClock_mul a c ha n) (tendsto_soninCrossingClock a c))

end RHTower
