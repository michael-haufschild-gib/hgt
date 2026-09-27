import GaloisForLFunctions.RHTower.HorizontallyIsolatedSimpleZeros

/-!
# Two thirds of the zeta zeros sit in a lens free of non-simple and off-line zeros

For a scale `L > 0` and an ordinate `γ`, the *lens* `𝓛_L(γ)` is the set of points `ρ'` with

`|Im ρ' − γ|·L/2 ≤ π/2`  and  `cosh((Re ρ' − ½)·L/2) ≤ 2 cos²((Im ρ' − γ)·L/2)`.

It contains the horizontal segment `|Re ρ' − ½| ≤ 5/(2L)` at height `γ` and the rectangle
`|Im ρ' − γ| ≤ 1/L`, `|Re ρ' − ½| ≤ 3/(2L)` (`inLens_of_rect`).  The main theorem
`lensIsolated_simple_critical` states: for every `ε > 0` and all large `T`, at least
`(HD(1) − ε)·N(T,2T)` zeros `ρ` with `T < Im ρ ≤ 2T` are simple, lie on the critical line, and every
other zero in the lens `𝓛_{log(T/2π)}(Im ρ)` is also simple and on the critical line.  Here
`HD(1) = 2 − 1/c₁* = 0.67250…` is the Montgomery–Taylor constant of Zeta23.

Proof.  In Zeta23's multiplicity-aware zero side, a simple critical zero `x` whose lens contains a
multiple critical zero or an off-line zero `z` costs nothing in the count `4 tr − ‖·‖² − 2N ≤ s₁`:
the normalised real vector `g` of `z` lies in the absorbing span, and `lens_overlap_cost` gives
`0 ≤ 1 + 2⟨f_x, g⟩²/‖g‖² − 2‖f_x‖²` (`absorbed_block_count`).  The windows, the tail seam and the
prime-side traces are Zeta23's (`thmD_count_of_seam`).
-/

open Complex Finset
open scoped RealInnerProductSpace
open Zeta23 Zeta23.ZeroSide

namespace RHTower

noncomputable section

/-- The lens at scale `L` around the ordinate `γ`. -/
def InLens (L γ : ℝ) (ρ' : ℂ) : Prop :=
  |ρ'.im - γ| * (L / 2) ≤ Real.pi / 2 ∧
    Real.cosh ((ρ'.re - 1 / 2) * (L / 2)) ≤ 2 * Real.cos ((ρ'.im - γ) * (L / 2)) ^ 2

/-- A smaller scale gives a larger lens. -/
theorem InLens.mono {L L' γ : ℝ} {ρ' : ℂ} (hL' : 0 < L') (hLL : L' ≤ L) (h : InLens L γ ρ') :
    InLens L' γ ρ' := by
  obtain ⟨h1, h2⟩ := h
  have hL : 0 < L := lt_of_lt_of_le hL' hLL
  have hle : |ρ'.im - γ| * (L' / 2) ≤ |ρ'.im - γ| * (L / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  refine ⟨hle.trans h1, ?_⟩
  have hcosh : Real.cosh ((ρ'.re - 1 / 2) * (L' / 2)) ≤ Real.cosh ((ρ'.re - 1 / 2) * (L / 2)) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < L' / 2),
      abs_of_pos (by linarith : (0:ℝ) < L / 2)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hcos : Real.cos ((ρ'.im - γ) * (L / 2)) ≤ Real.cos ((ρ'.im - γ) * (L' / 2)) := by
    rw [← Real.cos_abs ((ρ'.im - γ) * (L / 2)), ← Real.cos_abs ((ρ'.im - γ) * (L' / 2))]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    · rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)]; linarith [Real.pi_pos]
    · rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < L' / 2),
        abs_of_pos (by linarith : (0:ℝ) < L / 2)]
      exact hle
  have hcos0 : 0 ≤ Real.cos ((ρ'.im - γ) * (L / 2)) := by
    rw [← Real.cos_abs]
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · linarith [abs_nonneg ((ρ'.im - γ) * (L / 2)), Real.pi_pos]
    · rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)]; exact h1
  have hsq : Real.cos ((ρ'.im - γ) * (L / 2)) ^ 2 ≤ Real.cos ((ρ'.im - γ) * (L' / 2)) ^ 2 :=
    pow_le_pow_left₀ hcos0 hcos 2
  linarith

/-- `cosh(3/4) ≤ 2 cos²(1/2)`. -/
theorem cosh_three_quarters_le : Real.cosh (3 / 4) ≤ 2 * Real.cos (1 / 2) ^ 2 := by
  have h1 := Real.cosh_le_exp_half_sq (3 / 4)
  have h2 : Real.exp ((3 / 4 : ℝ) ^ 2 / 2) ≤ 32 / 23 := by
    have hy : ((3 / 4 : ℝ) ^ 2 / 2) = 9 / 32 := by norm_num
    rw [hy]
    have h3 := Real.add_one_le_exp (-(9 / 32 : ℝ))
    have h4 : Real.exp (9 / 32 : ℝ) * Real.exp (-(9 / 32 : ℝ)) = 1 := by
      rw [← Real.exp_add]; simp
    have h5 : 0 < Real.exp (9 / 32 : ℝ) := Real.exp_pos _
    nlinarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := 1 / 2)
  have hc' : (7 / 8 : ℝ) ≤ Real.cos (1 / 2) := by nlinarith
  nlinarith

/-- **The rectangle inside the lens.**  `|Im ρ' − γ|·L ≤ 1` and `|Re ρ' − ½|·L ≤ 3/2` put `ρ'` in
the lens. -/
theorem inLens_of_rect {L γ : ℝ} {ρ' : ℂ} (hL : 0 < L) (h1 : |ρ'.im - γ| * L ≤ 1)
    (h2 : |ρ'.re - 1 / 2| * L ≤ 3 / 2) : InLens L γ ρ' := by
  refine ⟨?_, ?_⟩
  · have : |ρ'.im - γ| * (L / 2) ≤ 1 / 2 := by linarith
    linarith [Real.pi_gt_three]
  · have hcosh : Real.cosh ((ρ'.re - 1 / 2) * (L / 2)) ≤ Real.cosh (3 / 4) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)]
      rw [abs_of_pos (by norm_num : (0:ℝ) < 3 / 4)]
      linarith
    have hcos : Real.cos (1 / 2) ≤ Real.cos ((ρ'.im - γ) * (L / 2)) := by
      rw [← Real.cos_abs ((ρ'.im - γ) * (L / 2))]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      · linarith [Real.pi_gt_three]
      · rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2)]; linarith
    have hc0 : 0 ≤ Real.cos (1 / 2) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_gt_three])
        (by linarith [Real.pi_gt_three])
    have := pow_le_pow_left₀ hc0 hcos 2
    linarith [cosh_three_quarters_le]

/-- **The horizontal segment inside the lens.** -/
theorem inLens_of_horizontal {L γ : ℝ} {ρ' : ℂ} (hL : 0 < L) (him : ρ'.im = γ)
    (hre : |ρ'.re - 1 / 2| * L ≤ 5 / 2) : InLens L γ ρ' := by
  refine ⟨by rw [him, sub_self, abs_zero, zero_mul]; positivity, ?_⟩
  rw [him, sub_self, zero_mul, Real.cos_zero]
  have : Real.cosh ((ρ'.re - 1 / 2) * (L / 2)) ≤ Real.cosh (5 / 4) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_of_pos (by linarith : (0:ℝ) < L / 2),
      abs_of_pos (by norm_num : (0:ℝ) < 5 / 4)]
    linarith
  linarith [cosh_five_quarters_le_two]

variable {Z : ZeroConfig} {T : ℝ} {P : Params}

/-- A zero is *lens-isolated* at scale `L` if every other zero in its lens is simple and on the
critical line. -/
def LensIsolated (Z : ZeroConfig) (L : ℝ) (ρ : ℂ) : Prop :=
  ∀ ρ' ∈ Z.carrier, ρ' ≠ ρ → InLens L ρ.im ρ' → ρ'.re = 1 / 2 ∧ Z.mult ρ' = 1

/-- Simple critical-line zeros with ordinate in `(T₁, T₂]` that are lens-isolated at scale `L`. -/
def NisoLens (Z : ZeroConfig) (L T₁ T₂ : ℝ) : ℕ :=
  (Z.window T₁ T₂ ∩ ZeroConfig.onLine ∩ Z.simple ∩ {ρ | LensIsolated Z L ρ}).ncard

open scoped Classical in
/-- Simple on-line points of `I′` whose lens contains a multiple on-line point or an off-line pair
representative of `I′`. -/
def lensMixed (Z : ZeroConfig) (hconj : PhiHatConj T P) (L : ℝ) : Finset (ZI Z T) :=
  (blockData Z T P hconj).S₁.filter fun x =>
    ∃ z : ZI Z T, (z ∈ (blockData Z T P hconj).S₂ ∨
      z ∈ (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)).R) ∧ InLens L (x : ℂ).im (z : ℂ)

open scoped Classical in
theorem lensMixed_subset (hconj : PhiHatConj T P) (L : ℝ) :
    lensMixed Z hconj L ⊆ (blockData Z T P hconj).S₁ := Finset.filter_subset _ _

open scoped Classical in
theorem mem_lensMixed_spec (hconj : PhiHatConj T P) {L : ℝ} (x : {z // z ∈ lensMixed Z hconj L}) :
    ∃ z : ZI Z T, (z ∈ (blockData Z T P hconj).S₂ ∨
      z ∈ (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)).R) ∧
      InLens L ((x.1 : ZI Z T) : ℂ).im (z : ℂ) :=
  (Finset.mem_filter.mp x.2).2

/-- **A zero in the lens is absorbed.**  If `x` is on the line and `z` lies in the lens of `x` at
scale `L`, the normalised real vectors `f` of `x` and `g` of `z` satisfy
`0 ≤ 1 + 2⟨f,g⟩²/‖g‖² − 2‖f‖²`. -/
theorem blockOverlap_lens (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hL : 0 < P.L T)
    (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0) (ha : 0 < P.a T)
    {x z : ZI Z T} (hx : (x : ℂ).re = 1 / 2) (hz : InLens (P.L T) (x : ℂ).im (z : ℂ)) :
    0 ≤ 1 + 2 * ⟪blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) x,
          blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) z⟫ ^ 2
        / ‖blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) z‖ ^ 2
      - 2 * ‖blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) x‖ ^ 2 := by
  set c := P.a T * P.L T ^ 2 with hcdef
  set γ := (x : ℂ).im
  set γ' := (z : ℂ).im
  set ε := (z : ℂ).re - 1 / 2
  have hgz : gammaOf (z : ℂ) = (γ' : ℂ) - ε * I := gammaOf_eq_im_sub _
  have hgx : gammaOf (x : ℂ) = (γ : ℂ) := by
    rw [gammaOf_eq_im_sub, hx]; simp; rfl
  have h := lens_overlap_cost P T hL hc hsupp hconj hreal ha γ γ' ε hz.1 hz.2
  have hin : ⟪blockReVec (blockData Z T P hconj) c x, blockReVec (blockData Z T P hconj) c z⟫
      = ∑ k : Fin (P.d T), (P.phiHat T ((γ : ℂ) - P.tau T k)).re / Real.sqrt c
          * ((P.phiHat T ((γ' : ℂ) - ε * I - P.tau T k)).re / Real.sqrt c) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, blockReVec_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [blockData, mkData_v, evalVec, hgz, hgx]
    ring
  have hnz : ‖blockReVec (blockData Z T P hconj) c z‖ ^ 2
      = ∑ k : Fin (P.d T), ((P.phiHat T ((γ' : ℂ) - ε * I - P.tau T k)).re / Real.sqrt c) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [blockReVec_apply, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [blockData, mkData_v, evalVec, hgz]
  have hnx : ‖blockReVec (blockData Z T P hconj) c x‖ ^ 2
      = ∑ k : Fin (P.d T), ((P.phiHat T ((γ : ℂ) - P.tau T k)).re / Real.sqrt c) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [blockReVec_apply, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [blockData, mkData_v, evalVec, hgx]
  rw [hin, hnz, hnx]
  exact h

/-- **Quantitative absorption.**  If `x` is on the line and `|Im z − Im x|·L/2 ≤ π/2` with
`cos((Im z − Im x)L/2) > 0`, the normalised real vectors `f` of `x` and `g` of `z` satisfy
`2cos²((Im z − Im x)L/2)/cosh((Re z − ½)L/2) − 1 ≤ 1 + 2⟨f,g⟩²/‖g‖² − 2‖f‖²`. -/
theorem blockOverlap_ge (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hL : 0 < P.L T)
    (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0) (ha : 0 < P.a T)
    {x z : ZI Z T} (hx : (x : ℂ).re = 1 / 2)
    (hΔ : |(z : ℂ).im - (x : ℂ).im| * (P.L T / 2) ≤ Real.pi / 2)
    (hpos : 0 < Real.cos (((z : ℂ).im - (x : ℂ).im) * (P.L T / 2))) :
    2 * Real.cos (((z : ℂ).im - (x : ℂ).im) * (P.L T / 2)) ^ 2
        / Real.cosh (((z : ℂ).re - 1 / 2) * (P.L T / 2)) - 1
      ≤ 1 + 2 * ⟪blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) x,
          blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) z⟫ ^ 2
        / ‖blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) z‖ ^ 2
      - 2 * ‖blockReVec (blockData Z T P hconj) (P.a T * P.L T ^ 2) x‖ ^ 2 := by
  set c := P.a T * P.L T ^ 2 with hcdef
  set γ := (x : ℂ).im
  set γ' := (z : ℂ).im
  set ε := (z : ℂ).re - 1 / 2
  have hgz : gammaOf (z : ℂ) = (γ' : ℂ) - ε * I := gammaOf_eq_im_sub _
  have hgx : gammaOf (x : ℂ) = (γ : ℂ) := by
    rw [gammaOf_eq_im_sub, hx]; simp; rfl
  have h := lens_overlap_cost_ge P T hL hc hsupp hconj hreal ha γ γ' ε hΔ hpos
  have hin : ⟪blockReVec (blockData Z T P hconj) c x, blockReVec (blockData Z T P hconj) c z⟫
      = ∑ k : Fin (P.d T), (P.phiHat T ((γ : ℂ) - P.tau T k)).re / Real.sqrt c
          * ((P.phiHat T ((γ' : ℂ) - ε * I - P.tau T k)).re / Real.sqrt c) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, blockReVec_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [blockData, mkData_v, evalVec, hgz, hgx]
    ring
  have hnz : ‖blockReVec (blockData Z T P hconj) c z‖ ^ 2
      = ∑ k : Fin (P.d T), ((P.phiHat T ((γ' : ℂ) - ε * I - P.tau T k)).re / Real.sqrt c) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [blockReVec_apply, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [blockData, mkData_v, evalVec, hgz]
  have hnx : ‖blockReVec (blockData Z T P hconj) c x‖ ^ 2
      = ∑ k : Fin (P.d T), ((P.phiHat T ((γ : ℂ) - P.tau T k)).re / Real.sqrt c) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [blockReVec_apply, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [blockData, mkData_v, evalVec, hgx]
  rw [hin, hnz, hnx]
  exact h

/-- **Lens zero-side count.**  For the normalised sampled Weil matrix `Â` of the window `I′`,
`4 tr Â − ‖Â‖² − 2N(I′)` is at most the number of simple on-line points of `I′` whose lens at scale
`L` contains no multiple on-line point and no off-line point of `I′`. -/
theorem hatAz_lens (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hL : 0 < P.L T) (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0)
    (ha : 0 < P.a T) :
    4 * RHLinalg.rtrace (P.hat T (Z.Az P T)) - RHLinalg.frobSq (P.hat T (Z.Az P T))
      - 2 * (Z.NIprime T : ℝ)
      ≤ (((blockData Z T P hconj).S₁ \ lensMixed Z hconj (P.L T)).card : ℝ) := by
  have hc0 : 0 < P.a T * P.L T ^ 2 := by positivity
  rw [hat_Az_eq_hatP_add_hatQ Z T P hconj, NIprime_eq_mk Z T _ (evalVec_reflect hconj)]
  refine absorbed_block_count (blockData Z T P hconj)
    (mkPairReps Z T (evalVec Z T P) (evalVec_reflect hconj)) (P.a T * P.L T ^ 2)
    (lensMixed Z hconj (P.L T)) hc0 (lensMixed_subset hconj _)
    (fun z hz => sum_normSq_v_le Z T P hconj hreal hPois z hz)
    (fun x => (mem_lensMixed_spec hconj x).choose)
    (fun x => (mem_lensMixed_spec hconj x).choose_spec.1) ?_
  intro x
  have hspec := (mem_lensMixed_spec hconj x).choose_spec
  have hxS1 : (x : ZI Z T) ∈ (blockData Z T P hconj).S₁ := lensMixed_subset hconj _ x.2
  have hxon : ((x : ZI Z T) : ℂ).re = 1 / 2 := by
    have h := (Finset.mem_filter.mp hxS1).2.1
    exact (mkData_σ_eq_iff Z T _ _ _).mp h
  exact blockOverlap_lens hconj hreal hL hc hsupp ha hxon hspec.2

open scoped Classical in
/-- A simple on-line point of `I′` with ordinate in `(T, 2T]` outside `lensMixed` is lens-isolated,
provided the lens height `π/L` is at most `D₀(T)`. -/
theorem lensIsolated_of_not_mem_lensMixed (hconj : PhiHatConj T P) {L : ℝ} (hL : 0 < L)
    (hwin : Real.pi / L ≤ D0 T) {x : ZI Z T} (hxS1 : x ∈ (blockData Z T P hconj).S₁)
    (hxnot : x ∉ lensMixed Z hconj L) (h1 : T < (x : ℂ).im) (h2 : (x : ℂ).im ≤ 2 * T) :
    LensIsolated Z L (x : ℂ) := by
  intro ρ' hρ' hne hlens
  by_contra hbad
  apply hxnot
  refine Finset.mem_filter.mpr ⟨hxS1, ?_⟩
  -- the lens is inside the window `I′`
  have hdist : |ρ'.im - (x : ℂ).im| ≤ D0 T := by
    have h := hlens.1
    have : |ρ'.im - (x : ℂ).im| ≤ Real.pi / L := by
      rw [le_div_iff₀ hL]; linarith
    linarith
  have hρ'ZI : ρ' ∈ ZI Z T := by
    rw [mem_ZI, mem_ZIprime_iff]
    refine ⟨hρ', ?_, ?_⟩
    · have := (abs_le.mp hdist).1; linarith
    · have := (abs_le.mp hdist).2; linarith
  by_cases hon : ρ'.re = 1 / 2
  · -- a multiple on-line point
    have hm2 : 2 ≤ Z.mult ρ' := by
      have h1 := Z.one_le_mult ρ' hρ'
      have hne1 : Z.mult ρ' ≠ 1 := fun h => hbad ⟨hon, h⟩
      omega
    refine ⟨⟨ρ', hρ'ZI⟩, Or.inl ?_, hlens⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hm2⟩
    exact (mkData_σ_eq_iff Z T _ _ _).mpr hon
  · -- an off-line point: take the representative with `β > ½`
    rcases lt_or_gt_of_ne hon with hlt | hgt
    · refine ⟨⟨reflect ρ', reflect_mem_ZI Z T hρ'ZI⟩, Or.inr ?_, ?_⟩
      · simp only [mkPairReps, Finset.mem_filter, Finset.mem_univ, true_and,
          ZeroSide.reflect_re]
        linarith
      · refine ⟨?_, ?_⟩
        · simp only [ZeroSide.reflect_im]; exact hlens.1
        · simp only [ZeroSide.reflect_im, ZeroSide.reflect_re]
          rw [show (1 - ρ'.re - 1 / 2) * (L / 2) = -((ρ'.re - 1 / 2) * (L / 2)) by ring,
            Real.cosh_neg]
          exact hlens.2
    · exact ⟨⟨ρ', hρ'ZI⟩, Or.inr (by simp [mkPairReps]; linarith), hlens⟩

/-- **From `I′` to `(T, 2T]`.**  The simple on-line points of `I′` outside `lensMixed` whose
ordinate lies in `(T, 2T]` are lens-isolated, provided the lens height `π/L` is at most `D₀(T)`. -/
theorem card_S₁_sdiff_lensMixed_le (hconj : PhiHatConj T P) {L : ℝ} (hL : 0 < L)
    (hwin : Real.pi / L ≤ D0 T) :
    ((blockData Z T P hconj).S₁ \ lensMixed Z hconj L).card
      ≤ NisoLens Z L T (2 * T) + Assembly.NII Z T := by
  classical
  set A : Finset ℂ := ((blockData Z T P hconj).S₁ \ lensMixed Z hconj L).map
    (Function.Embedding.subtype _)
  have hcardA : A.card = ((blockData Z T P hconj).S₁ \ lensMixed Z hconj L).card :=
    Finset.card_map _
  set S := Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple ∩ {ρ | LensIsolated Z L ρ}
  set W₁ := Z.window (T - D0 T) T
  set W₂ := Z.window (2 * T) (2 * T + D0 T)
  have hsub : (A : Set ℂ) ⊆ S ∪ W₁ ∪ W₂ := by
    intro ρ hρ
    simp only [A, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at hρ
    obtain ⟨x, hx, rfl⟩ := hρ
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxS1, hxnot⟩ := hx
    have hxZI := (mem_ZIprime_iff Z T).mp ((mem_ZI Z T).mp x.2)
    have hxon : (x : ℂ).re = 1 / 2 :=
      (mkData_σ_eq_iff Z T _ _ _).mp (Finset.mem_filter.mp hxS1).2.1
    have hxm : Z.mult (x : ℂ) = 1 := (Finset.mem_filter.mp hxS1).2.2
    by_cases h1 : (x : ℂ).im ≤ T
    · exact Or.inl (Or.inr ⟨hxZI.1, hxZI.2.1, h1⟩)
    by_cases h2 : 2 * T < (x : ℂ).im
    · exact Or.inr ⟨hxZI.1, h2, hxZI.2.2⟩
    replace h1 : T < (x : ℂ).im := lt_of_not_ge h1
    replace h2 : (x : ℂ).im ≤ 2 * T := le_of_not_gt h2
    exact Or.inl (Or.inl ⟨⟨⟨⟨hxZI.1, h1, h2⟩, hxon⟩, hxm⟩,
      lensIsolated_of_not_mem_lensMixed hconj hL hwin hxS1 hxnot h1 h2⟩)
  have hfin : ∀ {T₁ T₂ : ℝ}, (Z.window T₁ T₂).Finite := fun {T₁ T₂} => Z.window_finite T₁ T₂
  have hSfin : S.Finite := hfin.subset (fun ρ h => h.1.1.1)
  calc ((blockData Z T P hconj).S₁ \ lensMixed Z hconj L).card = (A : Set ℂ).ncard := by
        rw [Set.ncard_coe_finset, hcardA]
    _ ≤ (S ∪ W₁ ∪ W₂).ncard := Set.ncard_le_ncard hsub ((hSfin.union hfin).union hfin)
    _ ≤ (S ∪ W₁).ncard + W₂.ncard := Set.ncard_union_le _ _
    _ ≤ S.ncard + W₁.ncard + W₂.ncard := by gcongr; exact Set.ncard_union_le _ _
    _ ≤ NisoLens Z L T (2 * T) + Assembly.NII Z T := by
        have e1 : S.ncard = NisoLens Z L T (2 * T) := rfl
        have e2 : W₁.ncard ≤ Z.N (T - D0 T) T := Z.Nd_le_N _ _
        have e3 : W₂.ncard ≤ Z.N (2 * T) (2 * T + D0 T) := Z.Nd_le_N _ _
        unfold Assembly.NII
        omega

/-- **Seam, lens count.** -/
theorem seam_lens (hT : 0 ≤ T) (hconj : PhiHatConj T P) (hreal : PhiHatReal T P)
    (hPois : PoissonSq T P) {θ₀ : ℝ} (hTl : Assembly.TailInputs Z P T θ₀) (ha : 0 < P.a T)
    (hL : 0 < P.L T) (hc : Continuous (P.phi T)) (hsupp : ∀ u, P.L T / 2 ≤ |u| → P.phi T u = 0)
    (hwin : Real.pi / P.L T ≤ D0 T) :
    4 * RHLinalg.rtrace (P.hat T (Z.Gz P T)) - RHLinalg.frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (RHLinalg.frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ NisoLens Z (P.L T) T (2 * T) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← Assembly.hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_lens (Z := Z) hconj hreal hPois hL hc hsupp ha
  have hpert := Assembly.ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : ((((blockData Z T P hconj).S₁ \ lensMixed Z hconj (P.L T)).card : ℕ) : ℝ)
      ≤ (NisoLens Z (P.L T) T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast card_S₁_sdiff_lensMixed_le hconj hL hwin
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

end

section ThmD

open Filter Asymptotics Topology Real RHLinalg Zeta23.ThmD Zeta23.Assembly

/-- **Theorem D for lens-isolated simple zeros, abstract.** -/
theorem thmD_lens_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
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
      (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ) ≤ NisoLens Z (P.L T) T (2 * T) := by
  refine thmD_count_of_seam Z H P hP hlam aT bT JT trG trG2 hTr hc0 hc ha θ₀ hTail hθ₀ hNII
    hGzGp hId hcalE (fun T => (NisoLens Z (P.L T) T (2 * T) : ℝ)) ?_
  have hlam0 := hP.lam_pos
  have hLtop := Assembly.tendsto_L_atTop P hlam0
  filter_upwards [hTail, hId, ha, eventually_ge_atTop (1:ℝ), eventually_l_pos, eventually_w8 hP,
    hLtop.eventually (eventually_ge_atTop Real.pi)]
    with T hTl hid ha2 hT1 hl h8 hLpi
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have haposD : 0 < (P.atD T).a T := by rw [hid.2.2]; linarith [ha2.1]
  have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
  have hW := admWindow_params hP h8
  have hcD : Continuous ((P.atD T).phi T) := by
    rw [Params.atD_phi_valid T hP]; exact hW.contDiff.continuous
  have hsuppD : ∀ u, (P.atD T).L T / 2 ≤ |u| → (P.atD T).phi T u = 0 := by
    intro u hu; rw [Params.atD_phi_valid T hP]; exact hW.support u hu
  have hwin : Real.pi / (P.atD T).L T ≤ D0 T := by
    rw [Params.atD_L, div_le_iff₀ hLpos]
    have hsq : 1 ≤ D0 T := by
      unfold D0; rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hT1
    nlinarith [Real.pi_pos]
  have h := seam_lens (Z := Z) hT0 (fun z => GzGp.phiHat_conj _ T z)
    (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqD hP h8) hTl haposD
    (by rw [Params.atD_L]; exact hLpos) hcD hsuppD hwin
  rw [Params.atD_L] at h
  exact h

/-- Fixed `λ ∈ (0,1)`, abstract zero configuration with the paper's inputs. -/
theorem thmD_lens_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ NisoLens Z (P.L T) T (2 * T) := by
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
  have h := thmD_lens_abstract Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII
    hGzGp hId hcalE
  simpa only [HD, one_div] using h

end ThmD

noncomputable section Zeta

open Filter Zeta23.ThmD

/-- A nontrivial zero `ρ` of `ζ` is *lens-isolated* at scale `L` if every other nontrivial zero in
its lens is simple and on the critical line. -/
def ZetaLensIsolated (L : ℝ) (ρ : ℂ) : Prop :=
  ∀ ρ' : ℂ, IsNontrivialZero ρ' → ρ' ≠ ρ → InLens L ρ.im ρ' → ρ'.re = 1 / 2 ∧ zeroMult ρ' = 1

/-- Simple critical-line zeros of `ζ` with `T₁ < γ ≤ T₂` that are lens-isolated at scale `L`. -/
def N0simpleLensIsolated (L T₁ T₂ : ℝ) : ℕ :=
  (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1} ∩ {ρ | ZetaLensIsolated L ρ}).ncard

theorem NisoLens_zetaZeroConfig (L T₁ T₂ : ℝ) :
    NisoLens zetaZeroConfig L T₁ T₂ = N0simpleLensIsolated L T₁ T₂ := rfl

/-- A smaller scale is a stronger isolation condition. -/
theorem N0simpleLensIsolated_mono {L L' : ℝ} (hL' : 0 < L') (hLL : L' ≤ L) (T₁ T₂ : ℝ) :
    N0simpleLensIsolated L' T₁ T₂ ≤ N0simpleLensIsolated L T₁ T₂ := by
  apply Set.ncard_le_ncard
  · rintro ρ ⟨hρ, hiso⟩
    exact ⟨hρ, fun ρ' h1 h2 h3 => hiso ρ' h1 h2 (h3.mono hL' hLL)⟩
  · exact (zetaZeroConfig.window_finite T₁ T₂).subset fun ρ hρ => hρ.1.1.1

/-- `ζ` at fixed `λ ∈ (0,1)`: `(HD(λ) − ε)·N(T,2T)` simple critical-line zeros are lens-isolated at
scale `λ log(T/2π)`. -/
theorem lensIsolated_simple_critical_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD lam - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simpleLensIsolated (lam * l T) T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have h := thmD_lens_lam_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1
  simpa [paramsOf, Params.L, NisoLens_zetaZeroConfig] using h

/-- **Lens-isolated simple zeros of ζ.**  For every `ε > 0` and all large `T`, at least
`(HD(1) − ε)·N(T,2T)` zeros `ρ` with `T < Im ρ ≤ 2T` are simple, lie on the critical line, and every
other nontrivial zero in the lens `𝓛_{log(T/2π)}(Im ρ)` is simple and on the critical line.  Here
`HD(1) = 2 − 1/c₁* = 0.67250…` is the Montgomery–Taylor constant. -/
theorem lensIsolated_simple_critical :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD 1 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simpleLensIsolated (l T) T (2 * T) := by
  refine eps_form_HD (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (N0simpleLensIsolated (l T) T (2 * T) : ℝ))
    (fun _ => Nat.cast_nonneg _) ?_
  intro lam hl1 hl2 ε hε
  obtain ⟨T₀, hT₀⟩ := lensIsolated_simple_critical_lam (by linarith) hl2 ε hε
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
  have hscale : lam * l T ≤ l T := by nlinarith
  have := hT₀ T hTT₀
  exact le_trans this
    (by exact_mod_cast N0simpleLensIsolated_mono (by positivity) hscale T (2 * T))

/-- **Explicit rectangle.**  For every `ε > 0` and all large `T`, at least `(HD(1) − ε)·N(T,2T)`
zeros `ρ = ½ + iγ` with `T < γ ≤ 2T` are simple, and every other nontrivial zero `ρ'` with
`|Im ρ' − γ| ≤ 1/log(T/2π)` and `|Re ρ' − ½| ≤ 3/(2 log(T/2π))` is simple and on the critical
line. -/
theorem rectIsolated_simple_critical :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD 1 - ε) * (Ncount T (2 * T) : ℝ) ≤
        ((zerosIn T (2 * T) ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1} ∩
          {ρ | ∀ ρ' : ℂ, IsNontrivialZero ρ' → ρ' ≠ ρ → |ρ'.im - ρ.im| * l T ≤ 1 →
            |ρ'.re - 1 / 2| * l T ≤ 3 / 2 → ρ'.re = 1 / 2 ∧ zeroMult ρ' = 1}).ncard : ℕ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := lensIsolated_simple_critical ε hε
  refine ⟨max T₀ (2 * Real.pi * Real.exp 1), fun T hT => ?_⟩
  have hTbig : 2 * Real.pi * Real.exp 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hTbig
  have hl : 0 < l T := by
    unfold l
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith [Real.pi_pos]
  have hsub : zerosIn T (2 * T) ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1} ∩
        {ρ | ZetaLensIsolated (l T) ρ} ⊆
      zerosIn T (2 * T) ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1} ∩
        {ρ | ∀ ρ' : ℂ, IsNontrivialZero ρ' → ρ' ≠ ρ → |ρ'.im - ρ.im| * l T ≤ 1 →
          |ρ'.re - 1 / 2| * l T ≤ 3 / 2 → ρ'.re = 1 / 2 ∧ zeroMult ρ' = 1} := by
    rintro ρ ⟨hρ, hiso⟩
    exact ⟨hρ, fun ρ' h1 h2 h3 h4 => hiso ρ' h1 h2 (inLens_of_rect hl h3 h4)⟩
  have hcard := Set.ncard_le_ncard hsub
    ((zetaZeroConfig.window_finite T (2 * T)).subset fun ρ hρ => hρ.1.1.1)
  refine le_trans (hT₀ T (le_trans (le_max_left _ _) hT)) ?_
  unfold N0simpleLensIsolated
  exact_mod_cast hcard

end Zeta

end RHTower
