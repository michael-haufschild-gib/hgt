import GaloisForLFunctions.RHTower.HorizontalIsolationBlockPacket
import Zeta23.Assembly.SeamMult
import Zeta23.ThmD.Mult

/-!
# Two thirds of the zeta zeros are simple, critical and horizontally isolated

A zero `ρ = ½ + iγ` is *horizontally isolated at scale `δ`* if no other zero with ordinate `γ` lies
within horizontal distance `δ` of the critical line.  The main theorem
`horizontallyIsolated_simple_critical` states: for every `ε > 0` and all large `T`, at least
`(HD(1) − ε)·N(T,2T)` zeros with `T < γ ≤ 2T` are simple, on the critical line, and horizontally
isolated at scale `5/(2 log(T/2π))`.  Here `HD(1) = 2 − 1/c₁* = 0.67250…` is the unconditional
Montgomery–Taylor constant of Zeta23.

Proof.  Zeta23's multiplicity-aware zero side counts `s₁ ≥ 4 tr Â − ‖Â‖² − 2N` for the sampled Weil
matrix `Â`.  The unnormalised horizontal Lamzouri inequality (`HorizontalIsolationBlockPacket`)
removes from `s₁` every simple critical zero whose ordinate carries an off-line zero `p` with
`|Re p − ½| ≤ δ`.  This costs nothing once the sampled vector `f` of the critical zero and the real
part `g` of the sampled vector of `p` satisfy `0 ≤ 1 + 2⟨f,g⟩²/‖g‖² − 2‖f‖²`.  On the full sampling
grid, Parseval gives `⟨f,g⟩ = ∫φ²cosh(ε·)/∫φ² ≥ 1` and `‖g‖² ≤ 2⟨f,g⟩` when `cosh(εL/2) ≤ 2`, and
the overlap criterion passes this to the truncated grid (`blockOverlap_near`).  At `δ = 5/(2L)` the
condition is `cosh(5/4) ≤ 2`.  The
windows, the tail seam and the prime-side traces are Zeta23's, unchanged; only the counted set
differs (`seam_horizontal`, `thmD_horizontal_abstract`).
-/

open Complex Finset
open scoped RealInnerProductSpace
open Zeta23 Zeta23.ZeroSide

namespace RHTower

noncomputable section

variable (Z : ZeroConfig) (T : ℝ) (P : Params)

/-- A zero `ρ` is horizontally isolated at scale `δ` if no zero off the critical line shares its
ordinate within horizontal distance `δ` of the line. -/
def HorizIsolated (δ : ℝ) (ρ : ℂ) : Prop :=
  ∀ ρ' ∈ Z.carrier, ρ'.im = ρ.im → ρ'.re ≠ 1 / 2 → δ < |ρ'.re - 1 / 2|

/-- Simple critical-line zeros with ordinate in `(T₁, T₂]` that are horizontally isolated at
scale `δ`. -/
def NisoH (δ T₁ T₂ : ℝ) : ℕ :=
  (Z.window T₁ T₂ ∩ ZeroConfig.onLine ∩ Z.simple ∩ {ρ | HorizIsolated Z δ ρ}).ncard

variable {Z T P}

/-- Simple on-line points of the window `I′` that share their ordinate with an off-line pair within
horizontal distance `δ` of the line. -/
def nearMixed (Z : ZeroConfig) (hconj : PhiHatConj T P) (δ : ℝ) : Finset (ZI Z T) :=
  (blockData Z T P hconj).S₁.filter fun x =>
    ∃ p ∈ (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)).R,
      (p : ℂ).im = (x : ℂ).im ∧ |(p : ℂ).re - 1 / 2| ≤ δ

theorem nearMixed_subset (hconj : PhiHatConj T P) (δ : ℝ) :
    nearMixed Z hconj δ ⊆ (blockData Z T P hconj).S₁ := Finset.filter_subset _ _


omit T P in
theorem gammaOf_eq_im_sub (ρ : ℂ) :
    gammaOf ρ = ((ρ.im : ℝ) : ℂ) - ((ρ.re - 1 / 2 : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [gammaOf]

/-- **A near pair has large overlap.**  If `x` is on the line and `p` shares its ordinate with
`|Re p − 1/2| ≤ δ`, `cosh(δL/2) ≤ 2`, then the normalised real vectors `f` of `x` and `g` of `p`
satisfy `0 ≤ 1 + 2⟨f,g⟩²/‖g‖² − 2‖f‖²`. -/
theorem blockOverlap_near (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hL : 0 < P.L T)
    (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0) (ha : 0 < P.a T)
    {δ : ℝ} (hδ : Real.cosh (δ * (P.L T / 2)) ≤ 2) {x p : ZI Z T} (hx : (x : ℂ).re = 1 / 2)
    (him : (p : ℂ).im = (x : ℂ).im) (hre : |(p : ℂ).re - 1 / 2| ≤ δ) :
    0 ≤ 1 + 2 * ⟪blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) x,
          blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) p⟫ ^ 2
        / ‖blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) p‖ ^ 2
      - 2 * ‖blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) x‖ ^ 2 := by
  set c := P.a T * P.L T ^ 2 with hcdef
  set γ := (x : ℂ).im
  set ε := (p : ℂ).re - 1 / 2
  have hgp : gammaOf (p : ℂ) = (γ : ℂ) - ε * I := by rw [gammaOf_eq_im_sub, him]
  have hgx : gammaOf (x : ℂ) = (γ : ℂ) := by
    rw [gammaOf_eq_im_sub, hx]; simp; rfl
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hre
  have hε : Real.cosh (ε * (P.L T / 2)) ≤ 2 := by
    refine le_trans ?_ hδ
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hδ0]
    exact mul_le_mul_of_nonneg_right hre (abs_nonneg _)
  have h := shift_overlap_cost P T hL hc hsupp hconj hreal ha γ ε hε
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


theorem mem_nearMixed_spec (hconj : PhiHatConj T P) {δ : ℝ} (x : {z // z ∈ nearMixed Z hconj δ}) :
    ∃ p ∈ (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)).R,
      (p : ℂ).im = ((x.1 : ZI Z T) : ℂ).im ∧ |(p : ℂ).re - 1 / 2| ≤ δ :=
  (Finset.mem_filter.mp x.2).2

/-- **Horizontal zero-side count.**  For the normalised sampled Weil matrix `Â` of the window `I′`,
`4 tr Â − ‖Â‖² − 2N(I′)` is at most the number of simple on-line points of `I′` with no off-line
pair on their horizontal line within distance `δ` of the critical line, whenever
`cosh(δL/2) ≤ 2`. -/
theorem hatAz_horizontal (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hL : 0 < P.L T) (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0)
    (ha : 0 < P.a T) {δ : ℝ} (hδ : Real.cosh (δ * (P.L T / 2)) ≤ 2) :
    4 * RHLinalg.rtrace (P.hat T (Z.Az P T)) - RHLinalg.frobSq (P.hat T (Z.Az P T))
      - 2 * (Z.NIprime T : ℝ) ≤ (((blockData Z T P hconj).S₁ \ nearMixed Z hconj δ).card : ℝ) := by
  have hc0 : 0 < P.a T * P.L T ^ 2 := by positivity
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj, NIprime_eq_mk Z T _ (evalVec_reflect hconj)]
  let σ : {z // z ∈ nearMixed Z hconj δ} →
      {z // z ∈ (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)).R} :=
    fun x => ⟨(mem_nearMixed_spec hconj x).choose, (mem_nearMixed_spec hconj x).choose_spec.1⟩
  refine horizontal_block_count (blockData Z T P hconj)
    (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)) (P.a T * P.L T ^ 2)
    (nearMixed Z hconj δ) hc0 (nearMixed_subset hconj δ)
    (fun z hz => sum_normSq_v_le Z T P hconj hreal hPois z hz) σ ?_
  intro x
  have hspec := (mem_nearMixed_spec hconj x).choose_spec
  have hxS1 : (x : ZI Z T) ∈ (blockData Z T P hconj).S₁ := nearMixed_subset hconj δ x.2
  have hxon : ((x : ZI Z T) : ℂ).re = 1 / 2 := by
    have h := (Finset.mem_filter.mp hxS1).2.1
    exact (mkData_σ_eq_iff Z T _ _ _).mp h
  exact blockOverlap_near hconj hreal hL hc hsupp ha hδ hxon hspec.2.1 hspec.2.2


/-- **From `I′` to `(T, 2T]`.**  The simple on-line points of `I′` outside `nearMixed` are
horizontally isolated at scale `δ` when their ordinate lies in `(T, 2T]`; the others lie in
`I′ ∖ I`. -/
theorem card_S₁_sdiff_nearMixed_le (hconj : PhiHatConj T P) (δ : ℝ) :
    ((blockData Z T P hconj).S₁ \ nearMixed Z hconj δ).card ≤ NisoH Z δ T (2 * T) + Assembly.NII Z T := by
  classical
  set A : Finset ℂ := ((blockData Z T P hconj).S₁ \ nearMixed Z hconj δ).map (Function.Embedding.subtype _)
  have hcardA : A.card = ((blockData Z T P hconj).S₁ \ nearMixed Z hconj δ).card := Finset.card_map _
  set S := Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple ∩ {ρ | HorizIsolated Z δ ρ}
  set W₁ := Z.window (T - D0 T) T
  set W₂ := Z.window (2 * T) (2 * T + D0 T)
  have hsub : (A : Set ℂ) ⊆ S ∪ W₁ ∪ W₂ := by
    intro ρ hρ
    simp only [A, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe] at hρ
    obtain ⟨x, hx, rfl⟩ := hρ
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxS1, hxnot⟩ := hx
    have hxZI := (mem_ZIprime_iff Z T).mp ((mem_ZI Z T).mp x.2)
    have hxon : (x : ℂ).re = 1 / 2 := (mkData_σ_eq_iff Z T _ _ _).mp (Finset.mem_filter.mp hxS1).2.1
    have hxm : Z.mult (x : ℂ) = 1 := (Finset.mem_filter.mp hxS1).2.2
    by_cases h1 : (x : ℂ).im ≤ T
    · exact Or.inl (Or.inr ⟨hxZI.1, hxZI.2.1, h1⟩)
    by_cases h2 : 2 * T < (x : ℂ).im
    · exact Or.inr ⟨hxZI.1, h2, hxZI.2.2⟩
    replace h1 : T < (x : ℂ).im := lt_of_not_ge h1
    replace h2 : (x : ℂ).im ≤ 2 * T := le_of_not_gt h2
    refine Or.inl (Or.inl ⟨⟨⟨⟨hxZI.1, h1, h2⟩, hxon⟩, hxm⟩, ?_⟩)
    intro ρ' hρ' him hre
    by_contra hle
    replace hle : |ρ'.re - 1 / 2| ≤ δ := le_of_not_gt hle
    apply hxnot
    refine Finset.mem_filter.mpr ⟨hxS1, ?_⟩
    have hρ'ZI : ρ' ∈ ZI Z T := (mem_ZI Z T).mpr ((mem_ZIprime_iff Z T).mpr
      ⟨hρ', by rw [him]; exact hxZI.2.1, by rw [him]; exact hxZI.2.2⟩)
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · refine ⟨⟨reflect ρ', reflect_mem_ZI Z T hρ'ZI⟩, ?_, ?_, ?_⟩
      · simp only [mkPairReps, Finset.mem_filter, Finset.mem_univ, true_and, ZeroSide.reflect_re]; linarith
      · simp only [ZeroSide.reflect_im]; exact him
      · simp only [ZeroSide.reflect_re]
        rw [show 1 - ρ'.re - 1 / 2 = -(ρ'.re - 1 / 2) by ring, abs_neg]; exact hle
    · exact ⟨⟨ρ', hρ'ZI⟩, by simp [mkPairReps]; linarith, him, hle⟩
  have hfin : ∀ {T₁ T₂ : ℝ}, (Z.window T₁ T₂).Finite := fun {T₁ T₂} => Z.window_finite T₁ T₂
  have hSfin : S.Finite := hfin.subset (fun ρ h => h.1.1.1)
  calc ((blockData Z T P hconj).S₁ \ nearMixed Z hconj δ).card = (A : Set ℂ).ncard := by
        rw [Set.ncard_coe_finset, hcardA]
    _ ≤ (S ∪ W₁ ∪ W₂).ncard := Set.ncard_le_ncard hsub ((hSfin.union hfin).union hfin)
    _ ≤ (S ∪ W₁).ncard + W₂.ncard := Set.ncard_union_le _ _
    _ ≤ S.ncard + W₁.ncard + W₂.ncard := by gcongr; exact Set.ncard_union_le _ _
    _ ≤ NisoH Z δ T (2 * T) + Assembly.NII Z T := by
        have e1 : S.ncard = NisoH Z δ T (2 * T) := rfl
        have e2 : W₁.ncard ≤ Z.N (T - D0 T) T := Z.Nd_le_N _ _
        have e3 : W₂.ncard ≤ Z.N (2 * T) (2 * T + D0 T) := Z.Nd_le_N _ _
        unfold Assembly.NII
        omega


/-- **Seam, horizontal count.**  The multiplicity-aware seam of Zeta23 with `N₀ˢ(T,2T)` replaced by
the number of simple critical-line zeros that are horizontally isolated at scale `δ`. -/
theorem seam_horizontal (hT : 0 ≤ T) (hconj : PhiHatConj T P) (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P) {θ₀ : ℝ} (hTl : Assembly.TailInputs Z P T θ₀) (ha : 0 < P.a T)
    (hL : 0 < P.L T) (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0)
    {δ : ℝ} (hδ : Real.cosh (δ * (P.L T / 2)) ≤ 2) :
    4 * RHLinalg.rtrace (P.hat T (Z.Gz P T)) - RHLinalg.frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (RHLinalg.frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ NisoH Z δ T (2 * T) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← Assembly.hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_horizontal (Z := Z) hconj hreal hPois hL hc hsupp ha hδ
  have hpert := Assembly.ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : ((((blockData Z T P hconj).S₁ \ nearMixed Z hconj δ).card : ℕ) : ℝ)
      ≤ (NisoH Z δ T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast card_S₁_sdiff_nearMixed_le hconj δ
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

end

section ThmD

open Filter Asymptotics Topology Real RHLinalg Zeta23.ThmD Zeta23.Assembly


/-- **Theorem D from a seam, abstract.**  With the window-realising parameters, any count `Cnt`
that dominates the multiplicity-aware seam eventually satisfies `(2 − c⁻¹ − ε)·N(T,2T) ≤ Cnt T`
for large `T`.  Only the seam depends on which zeros are counted; the traces, the tail and the
endgame are Zeta23's. -/
theorem thmD_count_of_seam (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) (Cnt : ℝ → ℝ)
    (hseam : ∀ᶠ T in atTop,
      4 * rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) - frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
        - θ₀ T / ((P.atD T).a T * (P.atD T).L T)
          * (4 + 2 * Real.sqrt (frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)))
            + θ₀ T / ((P.atD T).a T * (P.atD T).L T))
        ≤ Cnt T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ) ≤ Cnt T := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  -- the functions of T (abbreviations)
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr
  -- basic limits
  have hLtop := Assembly.tendsto_L_atTop P hlam0
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  ------------------------------------------------------------------
  -- (1) the main inequality, eventually in T
  ------------------------------------------------------------------
  have hmain : ∀ᶠ T in atTop, (2 - c⁻¹) * N T - err T ≤ Cnt T := by
    filter_upwards [hseam, hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_l_pos]
      with T hA hTl hGG hid ha2 hT₁ hT₂ hl
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    -- the hat-unit traces in terms of the abstract data
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
    have haL : (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA
    -- |tr Ĝ − N| ≤ R₁
    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)
    -- ‖Ĝ‖² ≤ cinv N + R₂
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]; simp only [hR₂]; linarith
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := N0star_lower_c hB₀ hA htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (2 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith
  ------------------------------------------------------------------
  -- (2) err = o(N)
  ------------------------------------------------------------------
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  -- R₁ = o(N)
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  -- cinv is eventually in [0, 2/c] and bounded
  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]; exact h.2
  -- R₂ = o(N)
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have := hcinvO.mul (isBigO_refl N atTop)
      simpa using this
    have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (this.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]
  -- N(I′∖I) = o(N)
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
  -- B → 0
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr; exact ha2.1
  -- the bracket and the constant-drift term
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using this.abs
  have herr_o : err =o[atTop] N := o5.add o6
  ------------------------------------------------------------------
  -- (3) conclude
  ------------------------------------------------------------------
  exact eps_form_of_isLittleO hmain (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o



/-- **Theorem D for horizontally isolated simple zeros, abstract.**  With the window-realising
parameters, `(2 − c⁻¹ − ε)·N(T,2T)` simple critical-line zeros with ordinate in `(T,2T]` have no
off-line zero on their horizontal line within distance `5/(2L)` of the critical line. -/
theorem thmD_horizontal_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ) ≤ NisoH Z (5 / (2 * P.L T)) T (2 * T) := by
  refine thmD_count_of_seam Z H P hP hlam aT bT JT trG trG2 hTr hc0 hc ha θ₀ hTail hθ₀ hNII
    hGzGp hId hcalE (fun T => (NisoH Z (5 / (2 * P.L T)) T (2 * T) : ℝ)) ?_
  have hlam0 := hP.lam_pos
  filter_upwards [hTail, hId, ha, eventually_ge_atTop (0:ℝ), eventually_l_pos, eventually_w8 hP]
    with T hTl hid ha2 hT0 hl h8
  have haposD : 0 < (P.atD T).a T := by rw [hid.2.2]; linarith [ha2.1]
  have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
  have hW := admWindow_params hP h8
  have hcD : Continuous ((P.atD T).phi T) := by
    rw [Params.atD_phi_valid T hP]; exact hW.contDiff.continuous
  have hsuppD : ∀ u, (P.atD T).L T / 2 ≤ |u| → (P.atD T).phi T u = 0 := by
    intro u hu; rw [Params.atD_phi_valid T hP]; exact hW.support u hu
  have hδD : Real.cosh (5 / (2 * P.L T) * ((P.atD T).L T / 2)) ≤ 2 := by
    rw [Params.atD_L, show 5 / (2 * P.L T) * (P.L T / 2) = 5 / 4 by field_simp; ring]
    exact cosh_five_quarters_le_two
  exact seam_horizontal (Z := Z) hT0 (fun z => GzGp.phiHat_conj _ T z)
    (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqD hP h8) hTl haposD hLpos hcD hsuppD hδD

/-- Fixed `λ ∈ (0,1)`, abstract zero configuration with the paper's inputs. -/
theorem thmD_horizontal_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ NisoH Z (5 / (2 * P.L T)) T (2 * T) := by
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have h := thmD_horizontal_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII
    hGzGp hId hcalE
  simpa only [HD, one_div] using h

end ThmD

noncomputable section Zeta

open Filter Zeta23.ThmD

/-- A nontrivial zero `ρ` of `ζ` is horizontally isolated at scale `δ` if every nontrivial zero off
the critical line with the same ordinate lies at horizontal distance more than `δ` from the line. -/
def ZetaHorizIsolated (δ : ℝ) (ρ : ℂ) : Prop :=
  ∀ ρ' : ℂ, IsNontrivialZero ρ' → ρ'.im = ρ.im → ρ'.re ≠ 1 / 2 → δ < |ρ'.re - 1 / 2|

/-- Simple critical-line zeros of `ζ` with `T₁ < γ ≤ T₂` that are horizontally isolated at
scale `δ`. -/
def N0simpleIsolated (δ T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1} ∩ {ρ | ZetaHorizIsolated δ ρ}).ncard

theorem NisoH_zetaZeroConfig (δ T₁ T₂ : ℝ) :
    NisoH zetaZeroConfig δ T₁ T₂ = N0simpleIsolated δ T₁ T₂ := rfl

/-- A larger isolation scale is a stronger condition. -/
theorem N0simpleIsolated_anti {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) (T₁ T₂ : ℝ) :
    N0simpleIsolated δ₂ T₁ T₂ ≤ N0simpleIsolated δ₁ T₁ T₂ := by
  apply Set.ncard_le_ncard
  · rintro ρ ⟨hρ, hiso⟩
    exact ⟨hρ, fun ρ' h1 h2 h3 => lt_of_le_of_lt h (hiso ρ' h1 h2 h3)⟩
  · exact (zetaZeroConfig.window_finite T₁ T₂).subset fun ρ hρ => hρ.1.1.1

/-- `ζ` at fixed `λ ∈ (0,1)`: `(HD(λ) − ε)·N(T,2T)` simple critical-line zeros are horizontally
isolated at scale `5/(2λ log(T/2π))`. -/
theorem horizontallyIsolated_simple_critical_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD lam - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simpleIsolated (5 / (2 * (lam * l T))) T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have h := thmD_horizontal_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1
  simpa [paramsOf, Params.L, NisoH_zetaZeroConfig] using h

/-- **Horizontally isolated simple zeros of ζ.**  For every `ε > 0` and all large `T`, at least
`(HD(1) − ε)·N(T,2T)` zeros `ρ` with `T < Im ρ ≤ 2T` are simple, lie on the critical line, and no
other nontrivial zero with the same ordinate lies within horizontal distance `5/(2 log(T/2π))` of
the critical line.  Here `HD(1) = 2 − 1/c₁* = 0.67250…` is the Montgomery–Taylor constant. -/
theorem horizontallyIsolated_simple_critical :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simpleIsolated (5 / (2 * l T)) T (2 * T) := by
  refine eps_form_HD (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (N0simpleIsolated (5 / (2 * l T)) T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) ?_
  intro lam hl1 hl2 ε hε
  obtain ⟨T₀, hT₀⟩ := horizontallyIsolated_simple_critical_lam (by linarith) hl2 ε hε
  refine ⟨max T₀ (2 * Real.pi * Real.exp 1), fun T hT => ?_⟩
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTbig : 2 * Real.pi * Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hTbig
  have hl : 1 ≤ l T := by
    unfold l
    rw [Real.le_log_iff_exp_le (div_pos hTpos (by positivity))]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hlam0 : 0 < lam := by linarith
  have hscale : 5 / (2 * l T) ≤ 5 / (2 * (lam * l T)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have := hT₀ T hTT₀
  exact le_trans this (by exact_mod_cast N0simpleIsolated_anti hscale T (2 * T))

end Zeta

end RHTower
