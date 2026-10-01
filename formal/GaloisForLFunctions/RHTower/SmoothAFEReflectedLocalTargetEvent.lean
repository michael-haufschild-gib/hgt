import GaloisForLFunctions.RHTower.SmoothAFEReflectedConditionalLocalTarget
import GaloisForLFunctions.RHTower.SteinhausPrefixTargetEvent
import GaloisForLFunctions.RHTower.SmoothAFEReflectedPrescribedCellEvent


open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace RHTower
open SteinhausModel

/-- Simultaneous bounded reflected targets have an arbitrarily small power cost inside a prescribed phase cell. -/
theorem exists_reflectedCarrier_phaseCell_localTarget
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j)))
    (S : Finset ℕ) (ω : Omega) (B₀ : ℕ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {M ε ρ : ℝ}
    (hM : 0 ≤ M) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ ω' : Omega, (∀ p ∈ S, ω' p = ω p) ∧
      ∃ r₀ : ℝ, ∃ K B : ℕ, ∃ δ c : ℝ,
        B₀ ≤ B ∧ δ ≤ δ₀ ∧ 0 < r₀ ∧ 0 < K ∧ 0 < δ ∧ 0 < c ∧
        ∀ᶠ N : ℕ in atTop,
          N < (N / (2 * K)) * (N / (2 * K)) ∧ B ≤ N / (2 * K) ∧
          ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
            ∀ r : ℝ, 0 < r → r ≤ r₀ →
            ∀ t : EuclideanSpace ℂ (Fin J), ‖t‖ ≤ M →
              c * (N : ℝ) ^ (-ε) ≤ steinhausMeasure.real
                (steinhausCharacterCell B (steinhausLogPhaseShift ω' (-tau)) δ ∩
                  {η | ‖steinhausHilbertCarrier
                    (fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient
                      (d j) (tau + b j) r N) N η - t‖ < ρ}) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  let T : ℝ := M + J
  have hT : 0 < T := by dsimp [T]; positivity
  let H : ℝ := 2 * J * T ^ 2 / ε
  have hH : 0 < H := by dsimp [H]; positivity
  have hexponent : 2 * J * T ^ 2 / H = ε := by dsimp [H]; field_simp
  obtain ⟨ω', hprefix, r₀, K, B, δ, m, hB₀, hδ₀le, hr₀, hK, hδ, hm, hevent⟩ :=
    exists_reflectedPrimalConditional_covariance_boundedCentre_subcell_event hJ d b hd hdhalf hinj S ω B₀ hδ₀ hH
  have hlocal := eventually_frozenReflectedCarrier_localTarget_ge (B := T) hJ d b hd hdhalf
    (show 0 < 2 * K by omega) hH hρ
  refine ⟨ω', hprefix, r₀, K, B, δ, m / 4, hB₀, hδ₀le, hr₀, hK, hδ, by positivity, ?_⟩
  filter_upwards [hevent, hlocal] with N heventN hlocalN
  refine ⟨heventN.1, heventN.2.1, ?_⟩
  intro tau htau r hr hrle t ht
  obtain ⟨E, hE, hmass, hcell, hretain, hgood⟩ := heventN.2.2 tau htau r hr hrle
  let a := fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N
  let A : Set Omega := {η | ‖steinhausHilbertCarrier a N η - t‖ < ρ}
  have hA : MeasurableSet A :=
    measurableSet_lt ((measurable_steinhausHilbertCarrier a N).sub measurable_const).norm measurable_const
  have hq : 0 ≤ (1 / 4 : ℝ) * (N : ℝ) ^ (-ε) := by positivity
  have hconditional (η : Omega) (hη : η ∈ E) :
      (1 / 4 : ℝ) * (N : ℝ) ^ (-ε) ≤
        steinhausMeasure.real {ξ | freezeSteinhausPrefix (Nat.primesLE (N / (2 * K))) η ξ ∈ A} := by
    have hbg : ‖steinhausHilbertSmoothCarrier a N (N / (2 * K)) η‖ ≤ (J : ℝ) := by
      have hs : ‖steinhausHilbertSmoothCarrier a N (N / (2 * K)) η‖ ^ 2 ≤ (J : ℝ) := by
        rw [EuclideanSpace.norm_sq_eq]
        calc
          _ ≤ ∑ _j : Fin J, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j _
            have hb := (hgood η hη).1 j
            change ‖steinhausSmoothCarrier (a j) N (N / (2 * K)) η‖ ^ 2 ≤ 1
            nlinarith [norm_nonneg (steinhausSmoothCarrier (a j) N (N / (2 * K)) η)]
          _ = (J : ℝ) := by simp
      nlinarith [norm_nonneg (steinhausHilbertSmoothCarrier a N (N / (2 * K)) η)]
    have hshift : ‖t - steinhausHilbertSmoothCarrier a N (N / (2 * K)) η‖ ≤ T :=
      (norm_sub_le _ _).trans (add_le_add ht hbg)
    simpa only [A, a, Set.mem_setOf_eq, hexponent] using
      hlocalN tau htau r hr η t heventN.1 hshift (hgood η hη).2
  have hint := measureReal_prefixEvent_inter_target_ge
    (Nat.primesLE (N / (2 * K))) hE hA hretain hq hconditional
  calc
    _ = ((1 / 4 : ℝ) * (N : ℝ) ^ (-ε)) * m := by ring
    _ ≤ ((1 / 4 : ℝ) * (N : ℝ) ^ (-ε)) * steinhausMeasure.real E :=
      mul_le_mul_of_nonneg_left hmass hq
    _ ≤ steinhausMeasure.real (E ∩ A) := hint
    _ ≤ _ := measureReal_mono (Set.inter_subset_inter hcell (Set.Subset.refl A))

/-- Every prescribed finite phase cell supports all bounded reflected targets with arbitrarily small power loss. -/
theorem exists_reflectedCarrier_prescribedPhase_localTarget
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j)))
    (P : ℕ) (ω : Omega) {δ M ε ρ : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ r₀ c : ℝ, 0 < r₀ ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ t : EuclideanSpace ℂ (Fin J), ‖t‖ ≤ M →
        c * (N : ℝ) ^ (-ε) ≤ steinhausMeasure.real
          (steinhausCharacterCell P (steinhausLogPhaseShift ω (-tau)) δ ∩
            {η | ‖steinhausHilbertCarrier
              (fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient
                (d j) (tau + b j) r N) N η - t‖ < ρ}) := by
  obtain ⟨ω', hprefix, r₀, K, B, δ', c, hPB, hδle, hr₀, _hK, _hδ', hc, hbound⟩ :=
    exists_reflectedCarrier_phaseCell_localTarget hJ d b hd hdhalf hinj
      (Nat.primesLE P) ω P hδ hM hε hρ
  refine ⟨r₀, c, hr₀, hc, ?_⟩
  filter_upwards [hbound] with N hN
  intro tau htau r hr hrle t ht
  refine (hN.2.2 tau htau r hr hrle t ht).trans (measureReal_mono ?_)
  intro η hη
  refine ⟨?_, hη.2⟩
  intro n hn
  have hcent : X n (steinhausLogPhaseShift ω' (-tau)) =
      X n (steinhausLogPhaseShift ω (-tau)) := by
    apply X_congr_of_eqOn_primeFactors
    intro p hp
    have hpP : p ∈ Nat.primesLE P := by
      apply Nat.mem_primesLE.mpr
      refine ⟨?_, Nat.prime_of_mem_primeFactors hp⟩
      exact (Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hn).1; omega)
        (Nat.dvd_of_mem_primeFactors hp)).trans (Finset.mem_Icc.mp hn).2
    simp only [steinhausLogPhaseShift, hprefix p hpP]
  rw [← hcent]
  exact (hη.1 n (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
    (Finset.mem_Icc.mp hn).2.trans hPB⟩)).trans_le hδle

end RHTower
