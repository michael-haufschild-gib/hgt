import GaloisForLFunctions.RHTower.HorizontallyIsolatedSimpleZeros
import GaloisForLFunctions.RHTower.HorizontalSimplicityDeficitCount
import GaloisForLFunctions.RHTower.HorizontalShiftOverlapExact

/-!
# The horizontal seam with overlap deficits

Every simple critical zero `x` of the window `I′` that shares its ordinate with an off-line zero
`p = β + iγ`, `β > ½`, is removed from Zeta23's count at the price of its overlap deficit
`1 − R(β − ½)`, where `R(ε) = 2J²/(I₀I₂)` is the equal-ordinate overlap ratio of the window
(`overlapRatio`, `shift_overlap_cost_exact`).  If the window satisfies
`1 − R(ε) ≤ κεL + κ₀` for all `ε > 0`, the deficits add up to at most
`κL Σ_{β > ½} (β − ½) + κ₀ N(I′)` (`hatAz_horizontal_deficit`, `seam_horizontal_deficit`).
-/

open Complex Finset
open scoped RealInnerProductSpace
open Zeta23 Zeta23.ZeroSide

namespace RHTower

noncomputable section

/-- The equal-ordinate overlap ratio `2J²/(I₀I₂)` of the window of `P` at height `T` and horizontal
displacement `ε`. -/
def overlapRatio (P : Params) (T ε : ℝ) : ℝ :=
  2 * (∫ u in (-(P.L T / 2))..(P.L T / 2), P.phi T u ^ 2 * Real.cosh (ε * u)) ^ 2
    / ((∫ u in (-(P.L T / 2))..(P.L T / 2), P.phi T u ^ 2)
      * ∫ u in (-(P.L T / 2))..(P.L T / 2), (P.phi T u * Real.cosh (ε * u)) ^ 2)

open Classical in
/-- The first off-line moment `Σ (β − ½)` over the distinct zeros with `β > ½` and ordinate in
`(T₁, T₂]`. -/
def offMoment (Z : ZeroConfig) (T₁ T₂ : ℝ) : ℝ :=
  ∑ ρ ∈ (Z.window_finite T₁ T₂).toFinset.filter (fun ρ => 1 / 2 < ρ.re), (ρ.re - 1 / 2)

theorem offMoment_nonneg (Z : ZeroConfig) (T₁ T₂ : ℝ) : 0 ≤ offMoment Z T₁ T₂ := by
  classical
  unfold offMoment
  refine Finset.sum_nonneg fun ρ hρ => ?_
  have := (Finset.mem_filter.mp hρ).2
  linarith

variable {Z : ZeroConfig} {T : ℝ} {P : Params}

/-- **Exact overlap of an equal-ordinate pair.**  If `x` is on the line and `p` shares its
ordinate, the normalised real vectors `f` of `x` and `g` of `p` satisfy
`R(Re p − ½) − 1 ≤ 1 + 2⟨f,g⟩²/‖g‖² − 2‖f‖²`. -/
theorem blockOverlap_ratio (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hL : 0 < P.L T)
    (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0) (ha : 0 < P.a T)
    {x p : ZI Z T} (hx : (x : ℂ).re = 1 / 2) (him : (p : ℂ).im = (x : ℂ).im) :
    overlapRatio P T ((p : ℂ).re - 1 / 2) - 1
      ≤ 1 + 2 * ⟪blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) x,
          blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) p⟫ ^ 2
        / ‖blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) p‖ ^ 2
      - 2 * ‖blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) x‖ ^ 2 := by
  set c := P.a T * P.L T ^ 2 with hcdef
  set γ := (x : ℂ).im
  set ε := (p : ℂ).re - 1 / 2
  have hgp : gammaOf (p : ℂ) = (γ : ℂ) - ε * I := by rw [gammaOf_eq_im_sub, him]
  have hgx : gammaOf (x : ℂ) = (γ : ℂ) := by
    rw [gammaOf_eq_im_sub, hx]; simp; rfl
  have h := shift_overlap_cost_exact P T hL hc hsupp hconj hreal ha γ ε
  have hin : ⟪blockReVec (blockData Z T P hconj) c x, blockReVec (blockData Z T P hconj) c p⟫
      = ∑ k : Fin (P.d T), (P.phiHat T ((γ : ℂ) - P.tau T k)).re / Real.sqrt c
          * ((P.phiHat T ((γ : ℂ) - ε * I - P.tau T k)).re / Real.sqrt c) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, blockReVec_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [blockData, mkData_v, evalVec, hgp, hgx]
    ring
  have hnp : ‖blockReVec (blockData Z T P hconj) c p‖ ^ 2
      = ∑ k : Fin (P.d T), ((P.phiHat T ((γ : ℂ) - ε * I - P.tau T k)).re / Real.sqrt c) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [blockReVec_apply, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [blockData, mkData_v, evalVec, hgp]
  have hnx : ‖blockReVec (blockData Z T P hconj) c x‖ ^ 2
      = ∑ k : Fin (P.d T), ((P.phiHat T ((γ : ℂ) - P.tau T k)).re / Real.sqrt c) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [blockReVec_apply, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [blockData, mkData_v, evalVec, hgx]
  rw [hin, hnp, hnx]
  exact h

/-- The pair representatives contribute at most the off-line moment of `I′`. -/
theorem sum_pairReps_le_offMoment (hconj : PhiHatConj T P) (s : Finset (ZI Z T))
    (hs : s ⊆ (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)).R) :
    ∑ p ∈ s, ((p : ℂ).re - 1 / 2) ≤ offMoment Z (T - D0 T) (2 * T + D0 T) := by
  classical
  unfold offMoment
  have e : ∑ p ∈ s, ((p : ℂ).re - 1 / 2)
      = ∑ ρ ∈ s.map (Function.Embedding.subtype _), (ρ.re - 1 / 2) := by
    rw [Finset.sum_map]; rfl
  rw [e]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hρ
    have hpR := hs hp
    simp only [mkPairReps, Finset.mem_filter, Finset.mem_univ, true_and] at hpR
    refine Finset.mem_filter.mpr ⟨?_, hpR⟩
    rw [Set.Finite.mem_toFinset]
    exact (mem_ZIprime_iff Z T).mp ((mem_ZI Z T).mp p.2) |> fun h => ⟨h.1, h.2.1, h.2.2⟩
  · intro ρ hρ _
    have := (Finset.mem_filter.mp hρ).2
    linarith

/-- The number of distinct zeros of `I′` is at most `N(I′)`. -/
theorem card_le_NIprime (hconj : PhiHatConj T P) (s : Finset (ZI Z T)) :
    (s.card : ℝ) ≤ (Z.NIprime T : ℝ) := by
  rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]
  have h1 : s.card ≤ (Finset.univ : Finset (ZI Z T)).card := Finset.card_le_univ s
  have h2 : (Finset.univ : Finset (ZI Z T)).card ≤ (blockData Z T P hconj).Ncount := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun z _ => (blockData Z T P hconj).one_le_m z
  exact_mod_cast h1.trans h2

/-- **Horizontal zero-side count with deficits.** -/
theorem hatAz_horizontal_deficit (hconj : PhiHatConj T P) (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P) (hL : 0 < P.L T) (hc : Continuous (P.phi T))
    (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0) (ha : 0 < P.a T) (δ : ℝ) {κ κ₀ : ℝ}
    (hκ1 : 0 ≤ κ) (hκ : 0 ≤ κ₀) (hdef : ∀ ε > 0, 1 - overlapRatio P T ε ≤ κ * (ε * P.L T) + κ₀) :
    4 * RHLinalg.rtrace (P.hat T (Z.Az P T)) - RHLinalg.frobSq (P.hat T (Z.Az P T))
      - 2 * (Z.NIprime T : ℝ)
      ≤ (((blockData Z T P hconj).S₁ \ nearMixed Z hconj δ).card : ℝ)
        + κ * P.L T * offMoment Z (T - D0 T) (2 * T + D0 T) + κ₀ * (Z.NIprime T : ℝ) := by
  classical
  have hc0 : 0 < P.a T * P.L T ^ 2 := by positivity
  set D := blockData Z T P hconj with hD
  set Pr := mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj) with hPr
  set M := nearMixed Z hconj δ with hM
  let σ : {z // z ∈ M} → {z // z ∈ Pr.R} :=
    fun x => ⟨(mem_nearMixed_spec hconj x).choose, (mem_nearMixed_spec hconj x).choose_spec.1⟩
  have hσim : ∀ x, ((σ x : ZI Z T) : ℂ).im = ((x : ZI Z T) : ℂ).im :=
    fun x => (mem_nearMixed_spec hconj x).choose_spec.2.1
  have hxon : ∀ x : {z // z ∈ M}, ((x : ZI Z T) : ℂ).re = 1 / 2 := fun x => by
    have h := (Finset.mem_filter.mp (nearMixed_subset hconj δ x.2)).2.1
    exact (mkData_σ_eq_iff Z T _ _ _).mp h
  have hσre : ∀ x, 1 / 2 < ((σ x : ZI Z T) : ℂ).re := fun x => by
    have h := (σ x).2
    simp only [hPr, mkPairReps, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  set ε : {z // z ∈ M} → ℝ := fun x => ((σ x : ZI Z T) : ℂ).re - 1 / 2 with hε
  set dfc : {z // z ∈ M} → ℝ := fun x => 1 - overlapRatio P T (ε x) with hdfc
  have hcount := absorbed_block_count_add_deficit D Pr (P.a T * P.L T ^ 2) M hc0
    (nearMixed_subset hconj δ) (fun z hz => sum_normSq_v_le Z T P hconj hreal hPois z hz)
    (fun x => (σ x : ZI Z T)) (fun x => Or.inr (σ x).2) dfc (fun x => by
      have h := blockOverlap_ratio hconj hreal hL hc hsupp ha (hxon x) (hσim x)
      simp only [hdfc, hε]
      linarith)
  -- the deficits
  have hsum : ∑ x, dfc x ≤ κ * P.L T * ∑ x, ε x + κ₀ * (M.card : ℝ) := by
    have h1 : ∑ x, dfc x ≤ ∑ x : {z // z ∈ M}, (κ * (ε x * P.L T) + κ₀) :=
      Finset.sum_le_sum fun x _ => hdef (ε x) (by simp only [hε]; linarith [hσre x])
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul] at h1
    have h2 : ∑ x : {z // z ∈ M}, κ * (ε x * P.L T) = κ * P.L T * ∑ x, ε x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    linarith
  -- the displacements are those of distinct pair representatives
  have hinj : Function.Injective (fun x : {z // z ∈ M} => (σ x : ZI Z T)) := by
    intro x y hxy
    have h1 := hσim x
    have h2 := hσim y
    simp only at hxy
    rw [hxy] at h1
    apply Subtype.ext; apply Subtype.ext
    apply Complex.ext
    · rw [hxon x, hxon y]
    · rw [← h1, h2]
  have hεsum : ∑ x, ε x ≤ offMoment Z (T - D0 T) (2 * T + D0 T) := by
    have e : ∑ x, ε x = ∑ p ∈ Finset.univ.image (fun x : {z // z ∈ M} => (σ x : ZI Z T)),
        ((p : ℂ).re - 1 / 2) := by
      rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    rw [e]
    refine sum_pairReps_le_offMoment hconj _ ?_
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact (σ x).2
  have hMcard : (M.card : ℝ) ≤ (Z.NIprime T : ℝ) :=
    card_le_NIprime hconj M
  have hNI : (D.Ncount : ℝ) = (Z.NIprime T : ℝ) := by
    rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj]
  have hκL : 0 ≤ κ * P.L T := mul_nonneg hκ1 hL.le
  have e1 := mul_le_mul_of_nonneg_left hεsum hκL
  have e2 := mul_le_mul_of_nonneg_left hMcard hκ
  change 4 * RHLinalg.rtrace (D.blockP (P.a T * P.L T ^ 2) + D.blockQ (P.a T * P.L T ^ 2))
      - RHLinalg.frobSq (D.blockP (P.a T * P.L T ^ 2) + D.blockQ (P.a T * P.L T ^ 2))
      - 2 * (Z.NIprime T : ℝ) ≤ _
  linarith [hcount, hsum, e1, e2, hNI]

/-- **Seam with deficits.**  The multiplicity-aware seam of Zeta23 against the number of simple
critical zeros of `(T, 2T]` with no off-line zero on their horizontal line within distance `δ`,
plus the deficit terms. -/
theorem seam_horizontal_deficit (hT : 0 ≤ T) (hconj : PhiHatConj T P) (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P) {θ₀ : ℝ} (hTl : Assembly.TailInputs Z P T θ₀) (ha : 0 < P.a T)
    (hL : 0 < P.L T) (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0)
    (δ : ℝ) {κ κ₀ : ℝ} (hκ1 : 0 ≤ κ) (hκ : 0 ≤ κ₀)
    (hdef : ∀ ε > 0, 1 - overlapRatio P T ε ≤ κ * (ε * P.L T) + κ₀) :
    4 * RHLinalg.rtrace (P.hat T (Z.Gz P T)) - RHLinalg.frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (RHLinalg.frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ NisoH Z δ T (2 * T) + κ * P.L T * offMoment Z (T - D0 T) (2 * T + D0 T)
        + κ₀ * (Z.NIprime T : ℝ) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← Assembly.hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_horizontal_deficit (Z := Z) hconj hreal hPois hL hc hsupp ha δ hκ1 hκ hdef
  have hpert := Assembly.ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : ((((blockData Z T P hconj).S₁ \ nearMixed Z hconj δ).card : ℕ) : ℝ)
      ≤ (NisoH Z δ T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast card_S₁_sdiff_nearMixed_le hconj δ
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.NIprime_eq Z hT
  have hcore' := hcore
  rw [hNI] at hcore'
  linarith [hcore', hpert, hs1]

end

end RHTower
