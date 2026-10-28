import GaloisForLFunctions.ShallowCauchyPrimeEnergy.MultiscaleLorentzL2
import GaloisForLFunctions.RHTower.XiWardSourceWindowMultiplicity
import GaloisForLFunctions.RHTower.XiWardTriangularSourceRectangle
import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge
import GaloisForLFunctions.RHTower.ZetaDyadicWindowMomentTwoThirds

/-!
# Unconditional prime-side bound for the shallow Cauchy energy at depth `1 / log T`

This module resolves the shallow Cauchy energy problem unconditionally: for the global packet of
all strict-right `ξ`-zero copies (or distinct `ζ`/`ξ` zeros weighted by exact analytic
multiplicity) in `[T, 2T]` within horizontal distance `h` of the critical line, the `h`-shifted
Cauchy Gram energy `E_h` satisfies

`h · E_h ≤ C · max(κ₂, 2 h log T) · T log T`

uniformly for all `0 < h ≤ 1/64`, and in particular at the critical spacing `h = 1 / log T`:

`E_{1 / log T} ≤ C · T (log T)²`  and  `(1 / log T) · E_{1 / log T} ≤ C · T log T`,

eliminating the `log T` loss of the deterministic Riemann–von Mangoldt local ceiling (`T (log T)³`)
and matching the diagonal lower bound `(# shallow copies) · log T ≤ E_{1 / log T}` up to a constant
factor.

### Mechanism
1. **Kernel domination (`PoissonKernelDomination`):** For `0 < a, b ≤ h` and `R₀ = max(2h, κ₂ / log T)`,
   `4 h · transverseCauchyKernel (h + a) (h + b) Δ ≤ 4 · R₀² / (R₀² + Δ²)`.
2. **Line-reflection saving (`xiZeroCopyLineConjEquiv`):** Each strict-right copy `p` in `[T, 2T]`
   and its critical-line reflection `1 − conj(p)` are distinct elements of `dyadicZeroWindow T`
   with the same ordinate, so every shallow ordered pair `(p, q)` contributes four identical
   Lorentzian terms inside the global `dyadicZeroWindow T` pair sum, cancelling the prefactor `4`.
3. **Poisson semigroup + prime-cascade multiscale `L²` (`MultiscaleLorentzL2`):** Convolution
   `P_{R₀/2} ⋆ P_{R₀/2} = P_{R₀}` converts the Lorentzian pair sum into `(4 / (π R₀)) ∫ G_{R₀/2}²`,
   bounded unconditionally by `exists_dyadicZeroWindow_lorentzPairSum_le`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

/-! ## Centered coordinates and line-reflection geometry on `XiRightUpperZeroCopy` -/

theorem xiSpectralPoint_mul_I (c : XiZeroCopy) :
    I * xiSpectralPoint c = (c.1 : ℂ) - 1 / 2 := by
  rw [xiSpectralPoint]
  calc I * (((c.1 : ℂ) - 1 / 2) * (-I))
      = -((c.1 : ℂ) - 1 / 2) * (I * I) := by ring
    _ = (c.1 : ℂ) - 1 / 2 := by rw [Complex.I_mul_I]; ring

theorem xiRightCenteredZero_eq_sub_half (q : XiRightZeroCopy) :
    xiRightCenteredZero q = (q.1.1 : ℂ) - 1 / 2 :=
  xiSpectralPoint_mul_I q.1

theorem xiRightCenteredZero_re (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).re = (q.1.1 : ℂ).re - 1 / 2 := by
  rw [xiRightCenteredZero_eq_sub_half]
  simp

theorem xiRightCenteredZero_im (q : XiRightZeroCopy) :
    (xiRightCenteredZero q).im = (q.1.1 : ℂ).im := by
  rw [xiRightCenteredZero_eq_sub_half]
  simp

theorem im_xiZeroCopyLineConjEquiv (c : XiZeroCopy) :
    ((xiZeroCopyLineConjEquiv c).1 : ℂ).im = (c.1 : ℂ).im := by
  have h1 := congrArg Complex.im (xiSpectralPoint_mul_I (xiZeroCopyLineConjEquiv c))
  have h2 := congrArg Complex.im (xiSpectralPoint_mul_I c)
  simp only [Complex.sub_im, show (1 / 2 : ℂ).im = 0 by norm_num, sub_zero] at h1 h2
  rw [← h1, ← h2, xiSpectralPoint_lineConj]
  simp [Complex.mul_im]

theorem re_I_mul_xiSpectralPoint_lineConj (c : XiZeroCopy) :
    (I * xiSpectralPoint (xiZeroCopyLineConjEquiv c)).re = -(I * xiSpectralPoint c).re := by
  rw [xiSpectralPoint_lineConj]
  simp [Complex.mul_re]

/-- Embedding of strict-right upper zero copies into `XiZeroCopy` via critical-line reflection
`ρ ↦ 1 − conj(ρ)`, landing strictly to the left of the critical line at the same ordinate. -/
def xiRightUpperLineReflectedEmbedding : XiRightUpperZeroCopy ↪ XiZeroCopy :=
  xiRightUpperZeroCopyEmbedding.trans xiZeroCopyLineConjEquiv.toEmbedding

theorem im_xiRightUpperZeroCopyEmbedding (p : XiRightUpperZeroCopy) :
    ((xiRightUpperZeroCopyEmbedding p).1 : ℂ).im = (xiRightCenteredZero p.1).im :=
  (xiRightCenteredZero_im p.1).symm

theorem im_xiRightUpperLineReflectedEmbedding (p : XiRightUpperZeroCopy) :
    ((xiRightUpperLineReflectedEmbedding p).1 : ℂ).im = (xiRightCenteredZero p.1).im := by
  change ((xiZeroCopyLineConjEquiv p.1.1).1 : ℂ).im = (xiRightCenteredZero p.1).im
  rw [im_xiZeroCopyLineConjEquiv, xiRightCenteredZero_im]

theorem disjoint_map_rightUpper_lineReflected (S : Finset XiRightUpperZeroCopy) :
    Disjoint (S.map xiRightUpperZeroCopyEmbedding)
      (S.map xiRightUpperLineReflectedEmbedding) := by
  rw [Finset.disjoint_left]
  intro c hc₁ hc₂
  obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hc₁
  obtain ⟨q, _, hcq⟩ := Finset.mem_map.mp hc₂
  have hp_pos : 0 < (I * xiSpectralPoint p.1.1).re := p.1.2
  have hq_pos : 0 < (I * xiSpectralPoint q.1.1).re := q.1.2
  have hneg : (I * xiSpectralPoint (xiRightUpperLineReflectedEmbedding q)).re < 0 := by
    change (I * xiSpectralPoint (xiZeroCopyLineConjEquiv q.1.1)).re < 0
    rw [re_I_mul_xiSpectralPoint_lineConj]
    linarith
  rw [hcq] at hneg
  linarith

/-! ## Canonical dyadic strict-right, shallow, and deep windows -/

/-- All strict-right upper `ξ`-zero copies with ordinate in `[T, 2T]`. -/
def xiRightUpperWindow (T : ℝ) : Finset XiRightUpperZeroCopy :=
  (dyadicZeroWindow T).preimage xiRightUpperZeroCopyEmbedding
    xiRightUpperZeroCopyEmbedding.injective.injOn

theorem mem_xiRightUpperWindow_iff_mem_dyadic {T : ℝ} {p : XiRightUpperZeroCopy} :
    p ∈ xiRightUpperWindow T ↔ xiRightUpperZeroCopyEmbedding p ∈ dyadicZeroWindow T :=
  Finset.mem_preimage

theorem mem_xiRightUpperWindow {T : ℝ} (hT : 0 < T) {p : XiRightUpperZeroCopy} :
    p ∈ xiRightUpperWindow T ↔
      T ≤ (xiRightCenteredZero p.1).im ∧ (xiRightCenteredZero p.1).im ≤ 2 * T := by
  rw [mem_xiRightUpperWindow_iff_mem_dyadic, mem_dyadicZeroWindow hT,
    im_xiRightUpperZeroCopyEmbedding]

/-- All strict-right upper `ξ`-zero copies in `[T, 2T]` within horizontal depth `h` of the
critical line (`0 < Re ρ − 1/2 ≤ h`). -/
def xiShallowRightUpperWindow (h T : ℝ) : Finset XiRightUpperZeroCopy :=
  (xiRightUpperWindow T).filter fun p => (xiRightCenteredZero p.1).re ≤ h

/-- All strict-right upper `ξ`-zero copies in `[T, 2T]` strictly deeper than `h` from the
critical line (`Re ρ − 1/2 > h`). -/
def xiDeepRightUpperWindow (h T : ℝ) : Finset XiRightUpperZeroCopy :=
  (xiRightUpperWindow T).filter fun p => h < (xiRightCenteredZero p.1).re

theorem mem_xiShallowRightUpperWindow {h T : ℝ} (hT : 0 < T) {p : XiRightUpperZeroCopy} :
    p ∈ xiShallowRightUpperWindow h T ↔
      T ≤ (xiRightCenteredZero p.1).im ∧ (xiRightCenteredZero p.1).im ≤ 2 * T ∧
        (xiRightCenteredZero p.1).re ≤ h := by
  rw [xiShallowRightUpperWindow, Finset.mem_filter, mem_xiRightUpperWindow hT, and_assoc]

theorem mem_xiDeepRightUpperWindow {h T : ℝ} (hT : 0 < T) {p : XiRightUpperZeroCopy} :
    p ∈ xiDeepRightUpperWindow h T ↔
      T ≤ (xiRightCenteredZero p.1).im ∧ (xiRightCenteredZero p.1).im ≤ 2 * T ∧
        h < (xiRightCenteredZero p.1).re := by
  rw [xiDeepRightUpperWindow, Finset.mem_filter, mem_xiRightUpperWindow hT, and_assoc]

theorem card_xiRightUpperWindow_eq_shallow_add_deep (h T : ℝ) :
    (xiRightUpperWindow T).card =
      (xiShallowRightUpperWindow h T).card + (xiDeepRightUpperWindow h T).card := by
  classical
  have hdeep_eq : xiDeepRightUpperWindow h T =
      (xiRightUpperWindow T).filter (fun p => ¬ (xiRightCenteredZero p.1).re ≤ h) := by
    unfold xiDeepRightUpperWindow
    exact Finset.filter_congr fun _ _ => not_le.symm
  have hsum := Finset.sum_filter_add_sum_filter_not (xiRightUpperWindow T)
    (fun p : XiRightUpperZeroCopy => (xiRightCenteredZero p.1).re ≤ h) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
  rw [xiShallowRightUpperWindow, hdeep_eq, hsum]

/-! ## Canonical shallow Cauchy energy and bridges to `finiteOfflineCauchyEnergy` -/

/-- Exact `h`-shifted Cauchy Gram energy of all strict-right `ξ`-zero copies in `[T, 2T]` at
horizontal depth `≤ h`. -/
def xiShallowCauchyEnergy (h T : ℝ) : ℝ :=
  4 * ∑ p ∈ xiShallowRightUpperWindow h T, ∑ q ∈ xiShallowRightUpperWindow h T,
    transverseCauchyKernel
      (h + (xiRightCenteredZero p.1).re)
      (h + (xiRightCenteredZero q.1).re)
      ((xiRightCenteredZero p.1).im - (xiRightCenteredZero q.1).im)

theorem xiShallowCauchyEnergy_nonneg {h : ℝ} (hh : 0 < h) (T : ℝ) :
    0 ≤ xiShallowCauchyEnergy h T := by
  unfold xiShallowCauchyEnergy
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ?_)
  exact (transverseCauchyKernel_pos
    (add_pos hh (xiRightCenteredZero_re_pos p.1))
    (add_pos hh (xiRightCenteredZero_re_pos q.1)) _).le

/-- Any injective `Fin n`-indexed packet of strict-right upper copies in `[T, 2T]` at depth `≤ h`
has `finiteOfflineCauchyEnergy` bounded by `xiShallowCauchyEnergy h T`. -/
theorem finiteOfflineCauchyEnergy_xiRightUpper_le_xiShallowCauchyEnergy
    {n : ℕ} {h T : ℝ} (hh : 0 < h) (hT : 0 < T)
    (q : Fin n → XiRightUpperZeroCopy) (hq_inj : Function.Injective q)
    (hlo : ∀ j, T ≤ (xiRightCenteredZero (q j).1).im)
    (hhi : ∀ j, (xiRightCenteredZero (q j).1).im ≤ 2 * T)
    (hdepth : ∀ j, (xiRightCenteredZero (q j).1).re ≤ h) :
    finiteOfflineCauchyEnergy
      (fun j => h + (xiRightCenteredZero (q j).1).re)
      (fun j => (xiRightCenteredZero (q j).1).im)
      (fun _ => 1) ≤ xiShallowCauchyEnergy h T := by
  classical
  let emb : Fin n ↪ XiRightUpperZeroCopy := ⟨q, hq_inj⟩
  have hsub : Finset.univ.map emb ⊆ xiShallowRightUpperWindow h T := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hp
    exact (mem_xiShallowRightUpperWindow hT).mpr ⟨hlo j, hhi j, hdepth j⟩
  have hnn : ∀ p₁ p₂ : XiRightUpperZeroCopy,
      0 ≤ transverseCauchyKernel
        (h + (xiRightCenteredZero p₁.1).re)
        (h + (xiRightCenteredZero p₂.1).re)
        ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im) := fun p₁ p₂ =>
    (transverseCauchyKernel_pos
      (add_pos hh (xiRightCenteredZero_re_pos p₁.1))
      (add_pos hh (xiRightCenteredZero_re_pos p₂.1)) _).le
  unfold finiteOfflineCauchyEnergy xiShallowCauchyEnergy
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ j : Fin n, ∑ k : Fin n,
        ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) *
          transverseCauchyKernel
            (h + (xiRightCenteredZero (q j).1).re)
            (h + (xiRightCenteredZero (q k).1).re)
            ((xiRightCenteredZero (q j).1).im - (xiRightCenteredZero (q k).1).im)
      = ∑ p₁ ∈ Finset.univ.map emb, ∑ p₂ ∈ Finset.univ.map emb,
          transverseCauchyKernel
            (h + (xiRightCenteredZero p₁.1).re)
            (h + (xiRightCenteredZero p₂.1).re)
            ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im) := by
          simp only [Finset.sum_map, Nat.cast_one, one_mul]
          rfl
    _ ≤ ∑ p₁ ∈ Finset.univ.map emb, ∑ p₂ ∈ xiShallowRightUpperWindow h T,
          transverseCauchyKernel
            (h + (xiRightCenteredZero p₁.1).re)
            (h + (xiRightCenteredZero p₂.1).re)
            ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im) :=
        Finset.sum_le_sum fun p₁ _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p₂ _ _ => hnn p₁ p₂
    _ ≤ ∑ p₁ ∈ xiShallowRightUpperWindow h T, ∑ p₂ ∈ xiShallowRightUpperWindow h T,
          transverseCauchyKernel
            (h + (xiRightCenteredZero p₁.1).re)
            (h + (xiRightCenteredZero p₂.1).re)
            ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p₁ _ _ =>
          Finset.sum_nonneg fun p₂ _ => hnn p₁ p₂

/-- Exact enumeration identity: `xiShallowCauchyEnergy h T` equals `finiteOfflineCauchyEnergy` on
any bijection `Fin n ≃ xiShallowRightUpperWindow h T`. -/
theorem xiShallowCauchyEnergy_eq_finiteOfflineCauchyEnergy_of_equiv
    {n : ℕ} {h T : ℝ} (e : Fin n ≃ {p // p ∈ xiShallowRightUpperWindow h T}) :
    xiShallowCauchyEnergy h T =
      finiteOfflineCauchyEnergy
        (fun j => h + (xiRightCenteredZero (e j).1.1).re)
        (fun j => (xiRightCenteredZero (e j).1.1).im)
        (fun _ => 1) := by
  classical
  unfold xiShallowCauchyEnergy finiteOfflineCauchyEnergy
  congr 1
  rw [← Finset.sum_attach (xiShallowRightUpperWindow h T)]
  refine (Equiv.sum_comp e _).symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [← Finset.sum_attach (xiShallowRightUpperWindow h T)]
  refine (Equiv.sum_comp e _).symm.trans (Finset.sum_congr rfl fun k _ => ?_)
  simp

/-- Diagonal lower bound: `(# shallow copies) ≤ h · xiShallowCauchyEnergy h T`. -/
theorem card_xiShallowRightUpperWindow_le_shift_mul_energy
    {h : ℝ} (hh : 0 < h) (T : ℝ) :
    ((xiShallowRightUpperWindow h T).card : ℝ) ≤ h * xiShallowCauchyEnergy h T := by
  classical
  let n := (xiShallowRightUpperWindow h T).card
  let e : Fin n ≃ {p // p ∈ xiShallowRightUpperWindow h T} :=
    (Fintype.equivFinOfCardEq (by simp [n])).symm
  rw [xiShallowCauchyEnergy_eq_finiteOfflineCauchyEnergy_of_equiv e]
  exact xiRight_shallowLayer_card_le_shift_mul_finiteOfflineCauchyEnergy hh
    (fun j => (e j).1) (fun j => (Finset.mem_filter.mp (e j).2).2)

/-- Multiplicity fiber of `XiRightUpperZeroCopy` over a support zero `ρ : XiDivisorSupport`. -/
def xiRightUpperFiber (ρ : XiDivisorSupport) : Finset XiRightUpperZeroCopy :=
  (xiZeroCopyFiber ρ).preimage xiRightUpperZeroCopyEmbedding
    xiRightUpperZeroCopyEmbedding.injective.injOn

theorem map_xiRightUpperFiber_eq {ρ : XiDivisorSupport}
    (hre : 1 / 2 < (ρ : ℂ).re) (him : 0 < (ρ : ℂ).im) :
    (xiRightUpperFiber ρ).map xiRightUpperZeroCopyEmbedding = xiZeroCopyFiber ρ := by
  ext c
  simp only [xiRightUpperFiber, Finset.mem_map, Finset.mem_preimage]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact hp
  · intro hc
    have hc_eq : c.1 = ρ := mem_xiZeroCopyFiber.mp hc
    have hre_c : 0 < (I * xiSpectralPoint c).re := by
      rw [xiSpectralPoint_mul_I, hc_eq]
      simp only [Complex.sub_re, show (1 / 2 : ℂ).re = 1 / 2 by norm_num]
      linarith
    have him_c : 0 < (xiRightCenteredZero ⟨c, hre_c⟩).im := by
      rw [xiRightCenteredZero_im, hc_eq]
      exact him
    exact ⟨⟨⟨c, hre_c⟩, him_c⟩, hc, rfl⟩

theorem card_xiRightUpperFiber_eq_order_toNat {ρ : XiDivisorSupport}
    (hre : 1 / 2 < (ρ : ℂ).re) (him : 0 < (ρ : ℂ).im) :
    (xiRightUpperFiber ρ).card = (analyticOrderAt xi (ρ : ℂ)).toNat := by
  rw [← Finset.card_map xiRightUpperZeroCopyEmbedding, map_xiRightUpperFiber_eq hre him,
    card_xiZeroCopyFiber_eq_order_toNat]

/-- Any injective family `ρ : Fin n → ℂ` of distinct strict-right `ξ`-zeros in `[T, 2T]` within
depth `h` of the critical line, weighted by their exact analytic multiplicities
`m j = (analyticOrderAt xi (ρ j)).toNat`, has `finiteOfflineCauchyEnergy` bounded by
`xiShallowCauchyEnergy h T`. -/
theorem finiteOfflineCauchyEnergy_xiZeros_le_xiShallowCauchyEnergy
    {n : ℕ} {h T : ℝ} (hh : 0 < h) (hT : 0 < T)
    (ρ : Fin n → ℂ) (hρ_inj : Function.Injective ρ)
    (hxi : ∀ j, xi (ρ j) = 0)
    (hre_gt : ∀ j, 1 / 2 < (ρ j).re)
    (hre_le : ∀ j, (ρ j).re - 1 / 2 ≤ h)
    (him_lo : ∀ j, T ≤ (ρ j).im)
    (him_hi : ∀ j, (ρ j).im ≤ 2 * T) :
    finiteOfflineCauchyEnergy
      (fun j => h + ((ρ j).re - 1 / 2))
      (fun j => (ρ j).im)
      (fun j => (analyticOrderAt xi (ρ j)).toNat) ≤ xiShallowCauchyEnergy h T := by
  classical
  let supPt : Fin n → XiDivisorSupport := fun j => ⟨ρ j, mem_xi_divisor_support_of_eq_zero (hxi j)⟩
  let fib : Fin n → Finset XiRightUpperZeroCopy := fun j => xiRightUpperFiber (supPt j)
  have hfib_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) fib := by
    intro j₁ _ j₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp₁ hp₂
    have heq₁ : p.1.1.1 = supPt j₁ := mem_xiZeroCopyFiber.mp (Finset.mem_preimage.mp hp₁)
    have heq₂ : p.1.1.1 = supPt j₂ := mem_xiZeroCopyFiber.mp (Finset.mem_preimage.mp hp₂)
    have hval : ρ j₁ = ρ j₂ := congrArg Subtype.val (heq₁.symm.trans heq₂)
    exact hne (hρ_inj hval)
  have hfib_coord : ∀ (j : Fin n), ∀ p ∈ fib j,
      (xiRightCenteredZero p.1).re = (ρ j).re - 1 / 2 ∧
        (xiRightCenteredZero p.1).im = (ρ j).im := by
    intro j p hp
    have heq : p.1.1.1 = supPt j := mem_xiZeroCopyFiber.mp (Finset.mem_preimage.mp hp)
    have hval : (p.1.1.1 : ℂ) = ρ j := congrArg Subtype.val heq
    exact ⟨by rw [xiRightCenteredZero_re, hval], by rw [xiRightCenteredZero_im, hval]⟩
  have hfib_sub : Finset.univ.biUnion fib ⊆ xiShallowRightUpperWindow h T := by
    intro p hp
    obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hre_p, him_p⟩ := hfib_coord j p hpj
    exact (mem_xiShallowRightUpperWindow hT).mpr
      ⟨him_p.symm ▸ him_lo j, him_p.symm ▸ him_hi j, hre_p.symm ▸ hre_le j⟩
  have hfib_card : ∀ j : Fin n, (fib j).card = (analyticOrderAt xi (ρ j)).toNat := fun j =>
    card_xiRightUpperFiber_eq_order_toNat (hre_gt j) (hT.trans_le (him_lo j))
  have hnn : ∀ p₁ p₂ : XiRightUpperZeroCopy,
      0 ≤ transverseCauchyKernel
        (h + (xiRightCenteredZero p₁.1).re)
        (h + (xiRightCenteredZero p₂.1).re)
        ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im) := fun p₁ p₂ =>
    (transverseCauchyKernel_pos
      (add_pos hh (xiRightCenteredZero_re_pos p₁.1))
      (add_pos hh (xiRightCenteredZero_re_pos p₂.1)) _).le
  have hbi_eq :
      (∑ j : Fin n, ∑ k : Fin n,
          (((analyticOrderAt xi (ρ j)).toNat : ℝ) * ((analyticOrderAt xi (ρ k)).toNat : ℝ)) *
            transverseCauchyKernel
              (h + ((ρ j).re - 1 / 2)) (h + ((ρ k).re - 1 / 2)) ((ρ j).im - (ρ k).im)) =
        ∑ p₁ ∈ Finset.univ.biUnion fib, ∑ p₂ ∈ Finset.univ.biUnion fib,
          transverseCauchyKernel
            (h + (xiRightCenteredZero p₁.1).re)
            (h + (xiRightCenteredZero p₂.1).re)
            ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im) := by
    rw [Finset.sum_biUnion hfib_disj]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hinner :
        (∑ p₁ ∈ fib j, ∑ p₂ ∈ Finset.univ.biUnion fib,
            transverseCauchyKernel
              (h + (xiRightCenteredZero p₁.1).re)
              (h + (xiRightCenteredZero p₂.1).re)
              ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im)) =
          ∑ p₁ ∈ fib j, ∑ k : Fin n,
            ((analyticOrderAt xi (ρ k)).toNat : ℝ) *
              transverseCauchyKernel
                (h + ((ρ j).re - 1 / 2)) (h + ((ρ k).re - 1 / 2)) ((ρ j).im - (ρ k).im) := by
      refine Finset.sum_congr rfl fun p₁ hp₁ => ?_
      obtain ⟨hre₁, him₁⟩ := hfib_coord j p₁ hp₁
      rw [Finset.sum_biUnion hfib_disj]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hconst :
          (∑ p₂ ∈ fib k,
              transverseCauchyKernel
                (h + (xiRightCenteredZero p₁.1).re)
                (h + (xiRightCenteredZero p₂.1).re)
                ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im)) =
            ∑ _p₂ ∈ fib k,
              transverseCauchyKernel
                (h + ((ρ j).re - 1 / 2)) (h + ((ρ k).re - 1 / 2)) ((ρ j).im - (ρ k).im) := by
        refine Finset.sum_congr rfl fun p₂ hp₂ => ?_
        obtain ⟨hre₂, him₂⟩ := hfib_coord k p₂ hp₂
        rw [hre₁, him₁, hre₂, him₂]
      rw [hconst, Finset.sum_const, nsmul_eq_mul, hfib_card k]
    rw [hinner, Finset.sum_const, nsmul_eq_mul, hfib_card j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  unfold finiteOfflineCauchyEnergy xiShallowCauchyEnergy
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [hbi_eq]
  calc ∑ p₁ ∈ Finset.univ.biUnion fib, ∑ p₂ ∈ Finset.univ.biUnion fib,
        transverseCauchyKernel
          (h + (xiRightCenteredZero p₁.1).re)
          (h + (xiRightCenteredZero p₂.1).re)
          ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im)
      ≤ ∑ p₁ ∈ Finset.univ.biUnion fib, ∑ p₂ ∈ xiShallowRightUpperWindow h T,
          transverseCauchyKernel
            (h + (xiRightCenteredZero p₁.1).re)
            (h + (xiRightCenteredZero p₂.1).re)
            ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im) :=
        Finset.sum_le_sum fun p₁ _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hfib_sub fun p₂ _ _ => hnn p₁ p₂
    _ ≤ ∑ p₁ ∈ xiShallowRightUpperWindow h T, ∑ p₂ ∈ xiShallowRightUpperWindow h T,
          transverseCauchyKernel
            (h + (xiRightCenteredZero p₁.1).re)
            (h + (xiRightCenteredZero p₂.1).re)
            ((xiRightCenteredZero p₁.1).im - (xiRightCenteredZero p₂.1).im) :=
        Finset.sum_le_sum_of_subset_of_nonneg hfib_sub fun p₁ _ _ =>
          Finset.sum_nonneg fun p₂ _ => hnn p₁ p₂

/-! ## Line-reflection saving and domination by the global Lorentzian pair sum -/

/-- Because every `p ∈ xiShallowRightUpperWindow h T` and its line-reflected copy
`xiRightUpperLineReflectedEmbedding p` are distinct elements of `dyadicZeroWindow T` sharing the
same ordinate, `h · xiShallowCauchyEnergy h T` is bounded directly (with factor `1`, cancelling
the factor `4`) by the width-`R₀` Lorentzian pair sum on `dyadicZeroWindow T` whenever `2h ≤ R₀`. -/
theorem shift_mul_xiShallowCauchyEnergy_le_dyadic_lorentzPairSum
    {h T R₀ : ℝ} (hh : 0 < h) (hT : 0 < T) (hR : 2 * h ≤ R₀) :
    h * xiShallowCauchyEnergy h T ≤
      ∑ c₁ ∈ dyadicZeroWindow T, ∑ c₂ ∈ dyadicZeroWindow T,
        R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + ((c₁.1 : ℂ).im - (c₂.1 : ℂ).im) ^ (2 : ℕ)) := by
  classical
  let S := xiShallowRightUpperWindow h T
  let E₁ := S.map xiRightUpperZeroCopyEmbedding
  let E₂ := S.map xiRightUpperLineReflectedEmbedding
  have hdisj : Disjoint E₁ E₂ := disjoint_map_rightUpper_lineReflected S
  have hE₁_sub : E₁ ⊆ dyadicZeroWindow T := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hc
    exact mem_xiRightUpperWindow_iff_mem_dyadic.mp (Finset.mem_filter.mp hp).1
  have hE₂_sub : E₂ ⊆ dyadicZeroWindow T := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hc
    have hp_im := (mem_xiShallowRightUpperWindow hT).mp hp
    rw [mem_dyadicZeroWindow hT, im_xiRightUpperLineReflectedEmbedding]
    exact ⟨hp_im.1, hp_im.2.1⟩
  have hunion_sub : E₁ ∪ E₂ ⊆ dyadicZeroWindow T := Finset.union_subset hE₁_sub hE₂_sub
  have hstep1 :
      h * xiShallowCauchyEnergy h T ≤
        4 * ∑ p ∈ S, ∑ q ∈ S,
          R₀ ^ (2 : ℕ) /
            (R₀ ^ (2 : ℕ) + ((xiRightCenteredZero p.1).im - (xiRightCenteredZero q.1).im) ^ (2 : ℕ)) := by
    unfold xiShallowCauchyEnergy
    have hmul :
        h * (4 * ∑ p ∈ S, ∑ q ∈ S,
            transverseCauchyKernel
              (h + (xiRightCenteredZero p.1).re)
              (h + (xiRightCenteredZero q.1).re)
              ((xiRightCenteredZero p.1).im - (xiRightCenteredZero q.1).im)) =
          ∑ p ∈ S, ∑ q ∈ S,
            4 * h * transverseCauchyKernel
              (h + (xiRightCenteredZero p.1).re)
              (h + (xiRightCenteredZero q.1).re)
              ((xiRightCenteredZero p.1).im - (xiRightCenteredZero q.1).im) := by
      rw [← mul_assoc, mul_comm h 4, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    rw [hmul, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    exact shift_mul_transverseCauchyKernel_le_four_mul_lorentz hh
      (xiRightCenteredZero_re_pos p.1).le (Finset.mem_filter.mp hp).2
      (xiRightCenteredZero_re_pos q.1).le (Finset.mem_filter.mp hq).2 hR
  have hfour_eq :
      4 * (∑ p ∈ S, ∑ q ∈ S,
          R₀ ^ (2 : ℕ) /
            (R₀ ^ (2 : ℕ) + ((xiRightCenteredZero p.1).im - (xiRightCenteredZero q.1).im) ^ (2 : ℕ))) =
        ∑ c₁ ∈ E₁ ∪ E₂, ∑ c₂ ∈ E₁ ∪ E₂,
          R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + ((c₁.1 : ℂ).im - (c₂.1 : ℂ).im) ^ (2 : ℕ)) := by
    rw [Finset.sum_union hdisj]
    have hmap1 : ∀ c₁ : XiZeroCopy,
        (∑ c₂ ∈ E₁ ∪ E₂,
            R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + ((c₁.1 : ℂ).im - (c₂.1 : ℂ).im) ^ (2 : ℕ))) =
          2 * ∑ q ∈ S,
            R₀ ^ (2 : ℕ) /
              (R₀ ^ (2 : ℕ) + ((c₁.1 : ℂ).im - (xiRightCenteredZero q.1).im) ^ (2 : ℕ)) := by
      intro c₁
      rw [Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map]
      simp only [im_xiRightUpperZeroCopyEmbedding, im_xiRightUpperLineReflectedEmbedding]
      ring
    simp only [hmap1]
    rw [Finset.sum_map, Finset.sum_map]
    simp only [im_xiRightUpperZeroCopyEmbedding, im_xiRightUpperLineReflectedEmbedding]
    rw [← Finset.mul_sum]
    ring
  have hnn : ∀ c₁ c₂ : XiZeroCopy,
      0 ≤ R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + ((c₁.1 : ℂ).im - (c₂.1 : ℂ).im) ^ (2 : ℕ)) := by
    intro c₁ c₂; positivity
  calc h * xiShallowCauchyEnergy h T
      ≤ ∑ c₁ ∈ E₁ ∪ E₂, ∑ c₂ ∈ E₁ ∪ E₂,
          R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + ((c₁.1 : ℂ).im - (c₂.1 : ℂ).im) ^ (2 : ℕ)) := by
        rw [← hfour_eq]; exact hstep1
    _ ≤ ∑ c₁ ∈ E₁ ∪ E₂, ∑ c₂ ∈ dyadicZeroWindow T,
          R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + ((c₁.1 : ℂ).im - (c₂.1 : ℂ).im) ^ (2 : ℕ)) :=
        Finset.sum_le_sum fun c₁ _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hunion_sub fun c₂ _ _ => hnn c₁ c₂
    _ ≤ ∑ c₁ ∈ dyadicZeroWindow T, ∑ c₂ ∈ dyadicZeroWindow T,
          R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + ((c₁.1 : ℂ).im - (c₂.1 : ℂ).im) ^ (2 : ℕ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hunion_sub fun c₁ _ _ =>
          Finset.sum_nonneg fun c₂ _ => hnn c₁ c₂

/-! ## Main unconditional prime-side shallow Cauchy energy theorems -/

/-- **Uniform unconditional prime-side shallow Cauchy energy bound.**
There exist `C > 0` and `κ₂ ≥ 120000` such that eventually for large `T` and uniformly for every
depth `0 < h ≤ 1/64`,

`h · xiShallowCauchyEnergy h T ≤ C · max(κ₂, 2 h log T) · T log T`. -/
theorem exists_uniform_xiShallowCauchyEnergy_le :
    ∃ C κ₂ : ℝ, 0 < C ∧ 120000 ≤ κ₂ ∧ ∀ᶠ T : ℝ in atTop,
      ∀ h : ℝ, 0 < h → h ≤ 1 / 64 →
        h * xiShallowCauchyEnergy h T ≤
          C * max κ₂ (2 * h * Real.log T) * (T * Real.log T) := by
  obtain ⟨C_pair, κ₂, hCp, hκ₂, hev⟩ := exists_dyadicZeroWindow_lorentzPairSum_le
  refine ⟨C_pair, κ₂, hCp, hκ₂, ?_⟩
  filter_upwards [hev,
    Real.tendsto_log_atTop.eventually_ge_atTop (32 * κ₂),
    eventually_ge_atTop (4 : ℝ)] with T hpair hLbig hT4 h hh hh64
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  let R₀ := max (κ₂ / Real.log T) (2 * h)
  have hR₀_pos : 0 < R₀ := lt_max_of_lt_right (by positivity)
  have h2h_le : 2 * h ≤ R₀ := le_max_right _ _
  have hR₀_32 : R₀ ≤ 1 / 32 := by
    refine max_le ?_ (by linarith)
    rw [div_le_iff₀ hL0]
    linarith
  have hκ_le : κ₂ ≤ R₀ * Real.log T := by
    calc κ₂ = (κ₂ / Real.log T) * Real.log T := (div_mul_cancel₀ κ₂ hL0.ne').symm
      _ ≤ R₀ * Real.log T := mul_le_mul_of_nonneg_right (le_max_left _ _) hL0.le
  have hRL_eq : R₀ * Real.log T = max κ₂ (2 * h * Real.log T) := by
    dsimp [R₀]
    rw [max_mul_of_nonneg _ _ hL0.le, div_mul_cancel₀ κ₂ hL0.ne']
  calc h * xiShallowCauchyEnergy h T
      ≤ ∑ c₁ ∈ dyadicZeroWindow T, ∑ c₂ ∈ dyadicZeroWindow T,
          R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + ((c₁.1 : ℂ).im - (c₂.1 : ℂ).im) ^ (2 : ℕ)) :=
        shift_mul_xiShallowCauchyEnergy_le_dyadic_lorentzPairSum hh hT0 h2h_le
    _ ≤ C_pair * (R₀ * Real.log T) * (T * Real.log T) :=
        hpair R₀ hR₀_pos hR₀_32 hκ_le
    _ = C_pair * max κ₂ (2 * h * Real.log T) * (T * Real.log T) := by rw [hRL_eq]

/-- **Unconditional prime-side bound for the shallow Cauchy energy at depth `1 / log T`.**
There exists an absolute constant `C > 0` such that eventually for large `T`:
1. `xiShallowCauchyEnergy (1 / log T) T ≤ C · T (log T)²`,
2. `(1 / log T) · xiShallowCauchyEnergy (1 / log T) T ≤ C · T log T`,
3. `(# shallow strict-right copies in [T, 2T]) · log T ≤ xiShallowCauchyEnergy (1 / log T) T`. -/
theorem exists_xiShallowCauchyEnergy_one_div_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      xiShallowCauchyEnergy (1 / Real.log T) T ≤ C * T * (Real.log T) ^ (2 : ℕ) ∧
      (1 / Real.log T) * xiShallowCauchyEnergy (1 / Real.log T) T ≤ C * T * Real.log T ∧
      ((xiShallowRightUpperWindow (1 / Real.log T) T).card : ℝ) * Real.log T ≤
        xiShallowCauchyEnergy (1 / Real.log T) T := by
  obtain ⟨C₀, κ₂, hC₀, hκ₂, hev⟩ := exists_uniform_xiShallowCauchyEnergy_le
  refine ⟨C₀ * κ₂, by positivity, ?_⟩
  filter_upwards [hev,
    Real.tendsto_log_atTop.eventually_ge_atTop (64 : ℝ),
    eventually_ge_atTop (4 : ℝ)] with T hunif hL64 hT4
  have hL0 : 0 < Real.log T := by linarith
  have hh_pos : 0 < 1 / Real.log T := div_pos one_pos hL0
  have hh_64 : 1 / Real.log T ≤ 1 / 64 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  have hLne : Real.log T ≠ 0 := hL0.ne'
  have hmax : max κ₂ (2 * (1 / Real.log T) * Real.log T) = κ₂ := by
    have h2 : 2 * (1 / Real.log T) * Real.log T = 2 := by field_simp
    rw [h2]
    exact max_eq_left (by linarith)
  have hscaled : (1 / Real.log T) * xiShallowCauchyEnergy (1 / Real.log T) T ≤
      (C₀ * κ₂) * T * Real.log T := by
    have hb := hunif (1 / Real.log T) hh_pos hh_64
    rw [hmax] at hb
    linarith [show C₀ * κ₂ * (T * Real.log T) = (C₀ * κ₂) * T * Real.log T by ring]
  have hraw : xiShallowCauchyEnergy (1 / Real.log T) T ≤
      (C₀ * κ₂) * T * (Real.log T) ^ (2 : ℕ) := by
    have hm := mul_le_mul_of_nonneg_right hscaled hL0.le
    have hlhs : (1 / Real.log T) * xiShallowCauchyEnergy (1 / Real.log T) T * Real.log T =
        xiShallowCauchyEnergy (1 / Real.log T) T := by field_simp
    have hrhs : (C₀ * κ₂) * T * Real.log T * Real.log T =
        (C₀ * κ₂) * T * (Real.log T) ^ (2 : ℕ) := by ring
    linarith
  have hlow : ((xiShallowRightUpperWindow (1 / Real.log T) T).card : ℝ) * Real.log T ≤
      xiShallowCauchyEnergy (1 / Real.log T) T := by
    have hc := card_xiShallowRightUpperWindow_le_shift_mul_energy hh_pos T
    have hm := mul_le_mul_of_nonneg_right hc hL0.le
    have hrhs : (1 / Real.log T) * xiShallowCauchyEnergy (1 / Real.log T) T * Real.log T =
        xiShallowCauchyEnergy (1 / Real.log T) T := by field_simp
    linarith
  exact ⟨hraw, hscaled, hlow⟩

/-- **Unconditional `finiteOfflineCauchyEnergy` bound at depth `1 / log T` for arbitrary injective
packets of `XiRightUpperZeroCopy` in `[T, 2T]`.** -/
theorem exists_finiteOfflineCauchyEnergy_xiRightUpper_one_div_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (n : ℕ) (q : Fin n → XiRightUpperZeroCopy), Function.Injective q →
        (∀ j, T ≤ (xiRightCenteredZero (q j).1).im) →
        (∀ j, (xiRightCenteredZero (q j).1).im ≤ 2 * T) →
        (∀ j, (xiRightCenteredZero (q j).1).re ≤ 1 / Real.log T) →
          finiteOfflineCauchyEnergy
            (fun j => 1 / Real.log T + (xiRightCenteredZero (q j).1).re)
            (fun j => (xiRightCenteredZero (q j).1).im)
            (fun _ => 1) ≤ C * T * (Real.log T) ^ (2 : ℕ) := by
  obtain ⟨C, hC, hev⟩ := exists_xiShallowCauchyEnergy_one_div_log_le
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with T hE hT4 hL1 n q hq_inj hlo hhi hdepth
  exact (finiteOfflineCauchyEnergy_xiRightUpper_le_xiShallowCauchyEnergy
    (div_pos one_pos (by linarith)) (by linarith) q hq_inj hlo hhi hdepth).trans hE.1

/-- **Unconditional `finiteOfflineCauchyEnergy` bound at depth `1 / log T` for distinct strict-right
zeros of `riemannZeta` in `[T, 2T]` weighted by their exact analytic multiplicities.** -/
theorem exists_finiteOfflineCauchyEnergy_zetaZeros_one_div_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (n : ℕ) (ρ : Fin n → ℂ), Function.Injective ρ →
        (∀ j, riemannZeta (ρ j) = 0) →
        (∀ j, 1 / 2 < (ρ j).re) →
        (∀ j, (ρ j).re - 1 / 2 ≤ 1 / Real.log T) →
        (∀ j, T ≤ (ρ j).im) →
        (∀ j, (ρ j).im ≤ 2 * T) →
          finiteOfflineCauchyEnergy
            (fun j => 1 / Real.log T + ((ρ j).re - 1 / 2))
            (fun j => (ρ j).im)
            (fun j => (analyticOrderAt riemannZeta (ρ j)).toNat) ≤
              C * T * (Real.log T) ^ (2 : ℕ) := by
  obtain ⟨C, hC, hev⟩ := exists_xiShallowCauchyEnergy_one_div_log_le
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)]
    with T hE hT4 hL4 n ρ hρ_inj hzeta hre_gt hre_le him_lo him_hi
  have hT0 : 0 < T := by linarith
  have hh_pos : 0 < 1 / Real.log T := div_pos one_pos (by linarith)
  have hre_lt_one : ∀ j : Fin n, (ρ j).re < 1 := by
    intro j
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) (hzeta j)
  have hre_pos : ∀ j : Fin n, 0 < (ρ j).re := fun j => by linarith [hre_gt j]
  have hxi : ∀ j : Fin n, xi (ρ j) = 0 := fun j =>
    (xi_zero_iff_zeta_zero_of_mem_strip (hre_pos j) (hre_lt_one j)).mpr (hzeta j)
  have hmult_eq : (fun j : Fin n => (analyticOrderAt riemannZeta (ρ j)).toNat) =
      fun j : Fin n => (analyticOrderAt xi (ρ j)).toNat := by
    ext j
    rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre_pos j, hre_lt_one j⟩]
  rw [hmult_eq]
  exact (finiteOfflineCauchyEnergy_xiZeros_le_xiShallowCauchyEnergy hh_pos hT0 ρ hρ_inj
    hxi hre_gt hre_le him_lo him_hi).trans hE.1

end RHTower

end
