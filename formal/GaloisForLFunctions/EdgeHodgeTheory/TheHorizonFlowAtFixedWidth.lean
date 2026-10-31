import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeOfTheCompleteWeilFamily
import GaloisForLFunctions.HeckeKreinToeplitz.EveryReceiverAtEveryWidthIsBoundedByTheIndex
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion

/-!
# The horizon flow at fixed width

The complete Weil family lives on the plane of resolutions `(w, N)`: atoms of width `w` at the
points `log n`, `n ≤ N`. The complete Weil matrix at overlap `c` is the section `w = c/N`. At a
fixed width the families are **nested in the horizon**: the atoms up to `N` are among the atoms up
to `N' ≥ N`. This gives the horizon flow its integer invariants.

* **Monotonicity** (`horizonDefect_mono`): the Hodge defect `d_f(N)` — the negative squares of the
  Weil Gram matrix of the translates `f(· − log n)`, `n ≤ N` — is nondecreasing in `N`.
* **The conserved charge** (`iSup_horizonDefect`): `sup_N d_f(N)` is the number of zeros right of
  the critical line that `f` sees. Every finite family of rational positions becomes a family of
  integers after multiplication by a common denominator, and Weil's form is translation invariant,
  so the integer windows carry the whole index of the Hecke orbit kernel (HKT); the orbit kernel of
  a real test has exactly one negative square per seen right zero.
* **Stabilization** (`exists_horizonDefect_eq`): when the seen count is finite the defect reaches
  it at a finite horizon and stays there.
* **Positivity is the vanishing of the defect** (`horizonDefect_eq_zero_iff`): `d_f(N) = 0` iff
  Weil's form is nonnegative on every real atomic test `Σ_{n≤N} y_n f(· − log n)`. Real parts and
  imaginary parts of complex combinations are real atomic tests, and Weil's form on a complex test
  is the sum of its values on them.
* **The threshold** (`horizonThreshold`, `horizonDefect_eq_zero_iff_lt_horizonThreshold`): the
  horizon at which positivity first fails; positivity holds exactly below it. The threshold is `∞`
  iff the atom sees no right zero (`horizonThreshold_eq_top_iff`).
* **The section of the complete Weil family** (`positiveAt_iff_lt_horizonThreshold`): `W_{φ,c,N}` is
  positive semidefinite iff `N` is below the threshold of the atom of width `c/N`.
* **The detection horizon diverges as the atoms shrink** (`tendsto_horizonThreshold_tiltedUnitSpline`):
  for the tilted spline the threshold of the atom of width `w` tends to `∞` as `w → 0`.

So the edge is a curve in the `(w, N)` plane, the graph of the threshold. Along each horizontal
line the defect is a monotone integer converging to a charge that only the zeros can carry.
-/

noncomputable section

open Filter Topology Finset Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.EdgeHodgeTheory

open HTGeometry SpacingScaleHarmonicAnalysis ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory
open ArithmeticCastelnuovoSeveri (cx realTests weilGram weilGram_eq_zeroGram cx_contDiff
  cx_hasCompactSupport translate_contDiff translate_hasCompactSupport hermQuad_weilGram)
open ArithmeticOrientationGeometry (seenRightZeros)
open HeckeKreinToeplitz (gram orbitKernel gram_orbitKernel intWindow scale_intWindow
  negIndex_orbitKernel negIndex_eq_iSup_intWindow hermNegIndex_submatrix_le)
open Zeta23

/-! ### Weil's form on a complex test splits into its real and imaginary parts -/

open RHTower RHTower.WeilOneSided RHTower.WeilWorkPBAP Finsupp in
/-- `Re W(f, f) = Q(Re f) + Q(Im f)` for every complex test `f`. -/
theorem re_weilFull_eq_re_add_im (lam : ℕ → ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (weilFullFunctional lam (EF.weilTest f f)).re =
      weilQuadTw lam (fun u => (f u).re) + weilQuadTw lam (fun u => (f u).im) := by
  set F : WeilTestFn := ⟨f, hf, hfc⟩ with hFdef
  set R := paperRealPartTestFn F with hR
  set J := paperImagPartTestFn F with hJ
  have hsplit : paperSplitRealMixture (Finsupp.single F 1) =
      Finsupp.single R 1 + Finsupp.single J 1 := by
    simp [paperSplitRealMixture, hR, hJ, Finsupp.mapDomain_single]
  have hE := energy_paperSplitRealMixture (Finsupp.single F 1)
  have hD := defect_paperSplitRealMixture (Finsupp.single F 1)
  rw [hsplit] at hE hD
  simp only [WeilWorkPBAP.energy, WeilWorkPBAP.defect, map_add, linearCombination_single,
    one_smul] at hE hD
  have hF := re_weilFullFunctional_eq lam F
  have hRe := re_weilFullFunctional_eq lam R
  have hIm := re_weilFullFunctional_eq lam J
  have hRe' : (weilFullFunctional lam (EF.weilTest R.1 R.1)).re =
      weilQuadTw lam (fun u => (f u).re) := rfl
  have hIm' : (weilFullFunctional lam (EF.weilTest J.1 J.1)).re =
      weilQuadTw lam (fun u => (f u).im) := rfl
  have hfF : (weilFullFunctional lam (EF.weilTest f f)).re =
      (weilFullFunctional lam (EF.weilTest F.1 F.1)).re := rfl
  rw [hfF, hF, ← hE, ← hD, map_add]
  have : (weilFullFunctional lam (EF.weilTest R.1 R.1)).re +
      (weilFullFunctional lam (EF.weilTest J.1 J.1)).re =
      weilArchRe (EF.weilTest R.1 R.1) + weilArchRe (EF.weilTest J.1 J.1) -
        ((linearCombination ℝ (fun j : LogIndex => lam j)) (logVector R) +
          (linearCombination ℝ (fun j : LogIndex => lam j)) (logVector J)) := by
    rw [hRe, hIm]; ring
  rw [← this, hRe', hIm']

/-! ### The horizon family of a real test -/

/-- The Weil Gram matrix of the translates `f(· − log n)`, `1 ≤ n ≤ N`, of a real test. -/
def horizonGram (f : ℝ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    fun i : Fin N => ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1)) (cx f)

/-- **The Hodge defect of the horizon family**: the negative squares of its Weil Gram matrix. -/
def horizonDefect (f : ℝ → ℝ) (N : ℕ) : ℕ := hermNegIndex (horizonGram f N)

theorem horizonGram_eq_gram_orbitKernel {f : ℝ → ℝ} (hf : f ∈ realTests) (N : ℕ) :
    horizonGram f N = gram (orbitKernel zetaZeroConfig f) (intWindow N) := by
  rw [horizonGram, weilGram_eq_zeroGram _ (fun a => translate_contDiff (cx_contDiff hf.1) _)
    (fun a => translate_hasCompactSupport (cx_hasCompactSupport hf.2) _), gram_orbitKernel]
  simp only [scale_intWindow]

/-- The horizon families are nested. -/
theorem horizonGram_submatrix {f : ℝ → ℝ} {N N' : ℕ} (h : N ≤ N') :
    (horizonGram f N').submatrix (Fin.castLE h) (Fin.castLE h) = horizonGram f N := by
  ext i j
  simp [horizonGram, weilGram]

/-- **Monotonicity.** The Hodge defect is nondecreasing along the horizon flow. -/
theorem horizonDefect_mono (f : ℝ → ℝ) {N N' : ℕ} (h : N ≤ N') :
    horizonDefect f N ≤ horizonDefect f N' := by
  rw [horizonDefect, ← horizonGram_submatrix h]
  exact hermNegIndex_submatrix_le _ _

/-- **The conserved charge.** The supremum of the Hodge defect along the horizon flow is the number
of zeros right of the critical line that the test sees. -/
theorem iSup_horizonDefect {f : ℝ → ℝ} (hf : f ∈ realTests) :
    ⨆ N : ℕ, (horizonDefect f N : ℕ∞) = (seenRightZeros zetaZeroConfig f).encard := by
  rw [← negIndex_orbitKernel zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig hf,
    negIndex_eq_iSup_intWindow]
  simp only [horizonDefect, horizonGram_eq_gram_orbitKernel hf]

theorem horizonDefect_le_seen {f : ℝ → ℝ} (hf : f ∈ realTests) (N : ℕ) :
    (horizonDefect f N : ℕ∞) ≤ (seenRightZeros zetaZeroConfig f).encard :=
  (iSup_horizonDefect hf) ▸ le_iSup (fun N => (horizonDefect f N : ℕ∞)) N

/-- **Stabilization.** If the test sees finitely many right zeros, the Hodge defect reaches their
number at a finite horizon and keeps it. -/
theorem exists_horizonDefect_eq {f : ℝ → ℝ} (hf : f ∈ realTests)
    (hfin : (seenRightZeros zetaZeroConfig f).Finite) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (horizonDefect f N : ℕ∞) = (seenRightZeros zetaZeroConfig f).encard := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (seenRightZeros zetaZeroConfig f).encard = k :=
    ⟨_, (Set.Finite.encard_eq_coe_toFinset_card hfin)⟩
  have hsup := iSup_horizonDefect hf
  rw [hk] at hsup
  have hle : ∀ N, horizonDefect f N ≤ k := fun N => by
    have := le_iSup (fun N => (horizonDefect f N : ℕ∞)) N
    rw [hsup] at this
    exact_mod_cast this
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, horizonDefect f N₀ = k := by
    by_contra hne
    push_neg at hne
    have hlt : ∀ N, (horizonDefect f N : ℕ∞) ≤ (k - 1 : ℕ) := fun N => by
      have := lt_of_le_of_ne (hle N) (hne N)
      exact_mod_cast Nat.le_sub_one_of_lt this
    have := iSup_le hlt
    rw [hsup] at this
    have hk0 : k ≠ 0 := fun h0 => hne 0 (le_antisymm (h0 ▸ hle 0) (Nat.zero_le _))
    have : k ≤ k - 1 := by exact_mod_cast this
    omega
  refine ⟨N₀, fun N hN => ?_⟩
  rw [hk]
  exact_mod_cast le_antisymm (hle N) (hN₀ ▸ horizonDefect_mono f hN)

/-! ### Positivity of the horizon family -/

/-- The real atomic test with coefficients `y` is the real part of the combination of the
translates with coefficients `y`. -/
theorem atomicTest_eq_sum_fin (N : ℕ) (y : ℕ → ℝ) (f : ℝ → ℝ) (u : ℝ) :
    atomicTest N y f u = ∑ a : Fin N, y (a + 1) * f (u - Real.log ((a : ℝ) + 1)) := by
  unfold atomicTest
  rw [EffectiveArithmeticHodgeTheory.sum_Icc_one_eq_sum_fin]
  push_cast
  rfl

/-- **Positivity is the vanishing of the defect.** -/
theorem horizonDefect_eq_zero_iff {f : ℝ → ℝ} (hf : f ∈ realTests) (N : ℕ) :
    horizonDefect f N = 0 ↔ ∀ y : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N y f) := by
  have hT : ∀ a : Fin N, ContDiff ℝ 2
      (ArithmeticCastelnuovoSeveri.translate (Real.log ((a : ℝ) + 1)) (cx f)) :=
    fun a => translate_contDiff (cx_contDiff hf.1) _
  have hTc : ∀ a : Fin N, HasCompactSupport
      (ArithmeticCastelnuovoSeveri.translate (Real.log ((a : ℝ) + 1)) (cx f)) :=
    fun a => translate_hasCompactSupport (cx_hasCompactSupport hf.2) _
  -- the combination with coefficients `conj x`
  set G : (Fin N → ℂ) → ℝ → ℂ := fun x => ∑ a, conj (x a) •
    ArithmeticCastelnuovoSeveri.translate (Real.log ((a : ℝ) + 1)) (cx f) with hG
  have hGc : ∀ x, ContDiff ℝ 2 (G x) := fun x =>
    ContDiff.sum fun a _ => contDiff_const.smul (hT a)
  have hGcs : ∀ x, HasCompactSupport (G x) := fun x => by
    refine (HasCompactSupport.finset_sum (s := univ) fun a _ => ?_)
    exact (hTc a).smul_left
  have hquad : ∀ x, hermQuad (horizonGram f N) x =
      (RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (G x) (G x))).re := fun x =>
    hermQuad_weilGram _ _ hT hTc x
  -- the real and imaginary parts of a combination are real atomic tests
  have hpart : ∀ (x : Fin N → ℂ) (r : ℂ → ℝ), (r = Complex.re ∨ r = Complex.im) →
      ∃ y : ℕ → ℝ, (fun u => r (G x u)) = atomicTest N y f := by
    intro x r hr
    refine ⟨fun n => if hn : n - 1 < N then r (conj (x ⟨n - 1, hn⟩)) else 0, ?_⟩
    funext u
    rw [atomicTest_eq_sum_fin]
    simp only [hG, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ArithmeticCastelnuovoSeveri.translate, cx]
    rcases hr with rfl | rfl
    · rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [Complex.mul_re]
    · rw [Complex.im_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [Complex.mul_im]
  constructor
  · intro h0 y
    have h := ArithmeticCastelnuovoSeveri.hermQuad_nonneg_of_negIndex_eq_zero h0
      (fun a => ((y (a + 1) : ℝ) : ℂ))
    rw [hquad] at h
    have hGy : G (fun a => ((y (a + 1) : ℝ) : ℂ)) = cx (atomicTest N y f) := by
      funext u
      rw [atomicTest_eq_sum_fin]
      simp [hG, cx, ArithmeticCastelnuovoSeveri.translate, Finset.sum_apply]
    rwa [hGy] at h
  · intro H
    refine ArithmeticCastelnuovoSeveri.negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_
    rw [hquad, re_weilFull_eq_re_add_im _ (hGc x) (hGcs x)]
    obtain ⟨y₁, hy₁⟩ := hpart x Complex.re (Or.inl rfl)
    obtain ⟨y₂, hy₂⟩ := hpart x Complex.im (Or.inr rfl)
    have e₁ : weilQuadTw (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (fun u => (G x u).re) = weilQuad (atomicTest N y₁ f) := by rw [← hy₁]; rfl
    have e₂ : weilQuadTw (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (fun u => (G x u).im) = weilQuad (atomicTest N y₂ f) := by rw [← hy₂]; rfl
    rw [e₁, e₂]
    exact add_nonneg (H y₁) (H y₂)

/-! ### The threshold -/

/-- **The threshold** of a test: the first horizon at which its family has a negative square. -/
def horizonThreshold (f : ℝ → ℝ) : ℕ∞ := ⨅ (N : ℕ) (_ : horizonDefect f N ≠ 0), (N : ℕ∞)

/-- Positivity holds exactly below the threshold. -/
theorem horizonDefect_eq_zero_iff_lt_horizonThreshold (f : ℝ → ℝ) (N : ℕ) :
    horizonDefect f N = 0 ↔ (N : ℕ∞) < horizonThreshold f := by
  constructor
  · intro h0
    by_contra hge
    push_neg at hge
    have hlt : horizonThreshold f < (N + 1 : ℕ) := lt_of_le_of_lt hge (by exact_mod_cast N.lt_succ_self)
    obtain ⟨M, hM⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hM0, hMlt⟩ := iInf_lt_iff.mp hM
    have hMN : M ≤ N := by exact_mod_cast Order.le_of_lt_add_one (by exact_mod_cast hMlt)
    exact hM0 (Nat.eq_zero_of_le_zero (h0 ▸ horizonDefect_mono f hMN))
  · intro hlt
    by_contra h0
    exact absurd (iInf₂_le N h0) (not_le.mpr hlt)

/-- **The threshold is infinite iff the test sees no zero right of the line.** -/
theorem horizonThreshold_eq_top_iff {f : ℝ → ℝ} (hf : f ∈ realTests) :
    horizonThreshold f = ⊤ ↔ seenRightZeros zetaZeroConfig f = ∅ := by
  rw [← Set.encard_eq_zero, ← iSup_horizonDefect hf, ENat.iSup_eq_zero]
  simp only [horizonThreshold, iInf_eq_top, ENat.coe_ne_top, imp_false, not_not, Nat.cast_eq_zero]

/-! ### The section of the complete Weil family -/

theorem atomDilate_mem_realTests' {φ : ℝ → ℝ} (hφ : Admissible φ) {w : ℝ} (hw : 0 < w) :
    atomDilate φ w ∈ realTests := by
  obtain ⟨hg, -, hgc⟩ := atomDilate_facts hφ.contDiff hφ.supp hw
  exact ⟨hg, hgc⟩

/-- **The complete Weil family is a section of the threshold.** `W_{φ,c,N}` is positive
semidefinite iff `N` is below the threshold of the atom of width `c/N`. -/
theorem positiveAt_iff_lt_horizonThreshold {φ : ℝ → ℝ} (hφ : Admissible φ) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) :
    PositiveAt φ c N ↔ (N : ℕ∞) < horizonThreshold (atomDilate φ (c / N)) := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  rw [positiveAt_iff_twinPositiveAt hφ hc hN, ← horizonDefect_eq_zero_iff_lt_horizonThreshold,
    horizonDefect_eq_zero_iff (atomDilate_mem_realTests' hφ hw)]
  rfl

/-- **Width positivity is seeing.** At a fixed width the complete Weil family is positive at every
horizon iff its atom sees no zero right of the line. -/
theorem forall_positiveAt_width_iff {φ : ℝ → ℝ} (hφ : Admissible φ) {w : ℝ} (hw : 0 < w) :
    (∀ N : ℕ, 1 ≤ N → PositiveAt φ (w * N) N) ↔
      seenRightZeros zetaZeroConfig (atomDilate φ w) = ∅ := by
  rw [← horizonThreshold_eq_top_iff (atomDilate_mem_realTests' hφ hw)]
  constructor
  · intro H
    refine (horizonThreshold_eq_top_iff (atomDilate_mem_realTests' hφ hw)).mpr ?_
    rw [← Set.encard_eq_zero, ← iSup_horizonDefect (atomDilate_mem_realTests' hφ hw),
      ENat.iSup_eq_zero]
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [horizonDefect, hermNegIndex_eq_zero_of_isEmpty]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hcN : w * N / N = w := by field_simp
    have h := (positiveAt_iff_lt_horizonThreshold hφ (mul_pos hw hN0) hN).mp (H N hN)
    rw [hcN] at h
    exact_mod_cast (horizonDefect_eq_zero_iff_lt_horizonThreshold _ N).mpr h
  · intro htop N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hcN : w * N / N = w := by field_simp
    rw [positiveAt_iff_lt_horizonThreshold hφ (mul_pos hw hN0) hN, hcN, htop]
    exact ENat.coe_lt_top N

/-! ### The detection horizon diverges as the atoms shrink -/

/-- **The detection horizon diverges.** For the tilted spline the threshold of the atom of width
`w` tends to `∞` as `w → 0⁺`: positivity at every bounded overlap beyond one horizon puts each
small width below threshold at the horizon `⌈1/w⌉`. -/
theorem tendsto_horizonThreshold_tiltedUnitSpline :
    Tendsto (fun w => horizonThreshold (atomDilate tiltedUnitSpline w)) (𝓝[>] 0) (𝓝 ⊤) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_uniform_boundedOverlap
      2)
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro M
  have hδ : (0 : ℝ) < 1 / ((max N₀ M : ℕ) + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ] with w ⟨hw0, hw1⟩
  set N : ℕ := ⌈1 / w⌉₊ with hNdef
  have hwinv : ((max N₀ M : ℕ) : ℝ) + 1 < 1 / w := by
    rw [lt_div_iff₀ hw0]
    rw [lt_div_iff₀ (by positivity)] at hw1
    linarith
  have hN1 : 1 / w ≤ N := Nat.le_ceil _
  have hNlt : (N : ℝ) < 1 / w + 1 := Nat.ceil_lt_add_one (by positivity)
  have hNmax : max N₀ M < N := by exact_mod_cast hwinv.trans_le hN1
  have hN : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := w * N
  have hc0 : 0 < c := mul_pos hw0 hN0
  have hc2 : c ≤ 2 := by
    have : c < 1 + w := by
      have := mul_lt_mul_of_pos_left hNlt hw0
      rw [mul_add, mul_one_div_cancel hw0.ne', mul_one] at this
      exact this
    have hw1' : w ≤ 1 := by
      have : 1 / ((max N₀ M : ℕ) + 1 : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg (max N₀ M) : (0 : ℝ) ≤ _)]
      linarith
    linarith
  have hpos : PositiveAt tiltedUnitSpline c N := fun x =>
    RenormalizedIntersectionTheory.energy_nonneg_of_posDef (completeWeilMatrix_isHermitian _ _ _)
      (hN₀ N (by omega) c hc0 hc2) x
  have h := (positiveAt_iff_lt_horizonThreshold admissible_tiltedUnitSpline hc0 hN).mp hpos
  have hcN : c / N = w := by simp only [c]; field_simp
  rw [hcN] at h
  exact lt_trans (by exact_mod_cast (show M < N by omega)) h

end GaloisForLFunctions.EdgeHodgeTheory
