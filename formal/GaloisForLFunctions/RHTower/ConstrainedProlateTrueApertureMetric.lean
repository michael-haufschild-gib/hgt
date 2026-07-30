import GaloisForLFunctions.RHTower.ConstrainedProlateOperator
import GaloisForLFunctions.RHTower.Mollifier
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The true constrained-prolate aperture metric

The CCM aperture vector is

```text
u ↦ 1_[lambda⁻¹,lambda](u) * sum_(n≥1) f(nu).
```

Its ordinary `L²(du)` Gram is exactly the Hilbert Gram of
`E(f)(u)=sqrt(u) * sum_n f(nu)` in multiplicative Haar measure `du/u`.

This file constructs the actual finite aperture map on the existing `SoninL2` carrier and its
finite Gram matrices.  It also formalizes the finite divisor-Möbius reconstruction along one
multiplicative ray.  That reconstruction is the algebraic engine behind the exact central-radical
classification and the local `lambda⁻¹` coercivity estimate on the paper card.

No declaration asserts convergence to the fixed-Hermite Xi-moment target, a prolate asymptotic,
closed range of the aperture map, a Weil spectral floor, or RH.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexOrder InnerProduct

namespace RHTower

/-! ## The actual finite aperture operator -/

/-- The unnormalized dilation `f ↦ f(n ·)` on `L²(ℝ)`.  The zero index is defined as the zero
operator and never occurs in the aperture sums below. -/
def trueApertureRawDilation (n : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  if hn : 0 < n then
    ((Real.sqrt (n : ℝ))⁻¹ : ℂ) •
      dilationCLM (n : ℝ) (Nat.cast_pos.mpr hn)
  else 0

/-- The raw dilation really evaluates a representative at `n*x`, almost everywhere. -/
theorem trueApertureRawDilation_ae {n : ℕ} (hn : 0 < n) (f : SoninL2) :
    trueApertureRawDilation n f =ᵐ[volume]
      fun x : ℝ => f ((n : ℝ) * x) := by
  rw [trueApertureRawDilation, dif_pos hn]
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  simp only [_root_.smul_apply]
  filter_upwards [
    Lp.coeFn_smul (((Real.sqrt (n : ℝ))⁻¹ : ℂ))
      (dilationCLM (n : ℝ) hnR f),
    dilation_ae (n : ℝ) hnR f] with x hsmul hdilation
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hdilation' : (dilationCLM (n : ℝ) hnR f : SoninL2) x =
      (Real.sqrt (n : ℝ) : ℂ) * f ((n : ℝ) * x) := by
    simpa only [dilationCLM_apply] using hdilation
  rw [hdilation']
  rw [← mul_assoc]
  rw [inv_mul_cancel₀]
  · simp
  · exact_mod_cast Real.sqrt_ne_zero'.mpr hnR

/-- Finite CCM/Müntz summation, cut to the physical aperture `[a,b]`. -/
def trueApertureMuntzMap (a b : ℝ) (N : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Icc a b) measurableSet_Icc ∘L
    ∑ n ∈ Finset.Icc 1 N, trueApertureRawDilation n

/-- Almost-everywhere evaluation formula for the actual finite aperture map. -/
theorem trueApertureMuntzMap_ae (a b : ℝ) (N : ℕ) (f : SoninL2) :
    trueApertureMuntzMap a b N f =ᵐ[volume]
      (Icc a b).indicator
        (fun x : ℝ => ∑ n ∈ Finset.Icc 1 N, f ((n : ℝ) * x)) := by
  let T : SoninL2 →L[ℂ] SoninL2 :=
    ∑ n ∈ Finset.Icc 1 N, trueApertureRawDilation n
  have hsum : T f =ᵐ[volume]
      fun x : ℝ => ∑ n ∈ Finset.Icc 1 N, f ((n : ℝ) * x) := by
    have hterms :
        (fun x : ℝ => ∑ n ∈ Finset.Icc 1 N,
          (trueApertureRawDilation n f) x) =ᵐ[volume]
        fun x : ℝ => ∑ n ∈ Finset.Icc 1 N, f ((n : ℝ) * x) :=
      by
        have hraw :=
          eventuallyEq_sum (s := Finset.Icc 1 N) fun n hnMem =>
            trueApertureRawDilation_ae (Finset.mem_Icc.mp hnMem).1 f
        filter_upwards [hraw] with x hx
        simpa only [Finset.sum_apply] using hx
    have hcoe :
        ⇑(∑ n ∈ Finset.Icc 1 N, trueApertureRawDilation n f) =ᵐ[volume]
          fun x : ℝ => ∑ n ∈ Finset.Icc 1 N,
            (trueApertureRawDilation n f) x := by
      classical
      induction (Finset.Icc 1 N) using Finset.induction_on with
      | empty => simpa using! (Lp.coeFn_zero ℂ 2 volume)
      | @insert n s hn ih =>
          rw [Finset.sum_insert hn]
          filter_upwards [Lp.coeFn_add (trueApertureRawDilation n f)
              (∑ k ∈ s, trueApertureRawDilation k f), ih] with x hadd htail
          rw [hadd, Pi.add_apply, htail]
          simp [Finset.sum_insert hn]
    simpa only [T, _root_.sum_apply] using hcoe.trans hterms
  change indicatorCutoff (Icc a b) measurableSet_Icc (T f) =ᵐ[volume] _
  filter_upwards [indicatorCutoff_ae (Icc a b) measurableSet_Icc (T f), hsum] with x hcut hs
  rw [hcut]
  by_cases hx : x ∈ Icc a b <;> simp [hx, hs]

/-- The genuine CCM aperture map on the existing constrained prolate source space.  Compact
support makes the universal cutoff `floor(lambda²)` exact on `[lambda⁻¹,lambda]`. -/
def constrainedProlateTrueApertureMap (lambda : ℝ) :
    constrainedProlateSubspace lambda →L[ℂ] SoninL2 :=
  trueApertureMuntzMap lambda⁻¹ lambda ⌊lambda ^ 2⌋₊ ∘L
    (evenSubspace.subtypeL ∘L (constrainedProlateSubspace lambda).subtypeL)

/-- The pullback Hilbert Gram of two true aperture vectors. -/
def constrainedProlateTrueApertureGram (lambda : ℝ)
    (f g : constrainedProlateSubspace lambda) : ℂ :=
  inner ℂ (constrainedProlateTrueApertureMap lambda f)
    (constrainedProlateTrueApertureMap lambda g)

/-- A finite section of the true aperture metric is literally a Hilbert-space Gram matrix. -/
def constrainedProlateTrueApertureGramMatrix {N : ℕ} (lambda : ℝ)
    (v : Fin N → constrainedProlateSubspace lambda) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.gram ℂ (fun i => constrainedProlateTrueApertureMap lambda (v i))

theorem constrainedProlateTrueApertureGramMatrix_posSemidef {N : ℕ} (lambda : ℝ)
    (v : Fin N → constrainedProlateSubspace lambda) :
    (constrainedProlateTrueApertureGramMatrix lambda v).PosSemidef := by
  exact Matrix.posSemidef_gram ℂ _

theorem constrainedProlateTrueApertureGramMatrix_posDef_of_linearIndependent
    {N : ℕ} {lambda : ℝ} {v : Fin N → constrainedProlateSubspace lambda}
    (hli : LinearIndependent ℂ
      (fun i => constrainedProlateTrueApertureMap lambda (v i))) :
    (constrainedProlateTrueApertureGramMatrix lambda v).PosDef := by
  exact Matrix.posDef_gram_of_linearIndependent hli

/-! ## Finite Möbius recovery on one multiplicative ray -/

/-- The finite dilation tail `S_a(n)=sum_{n|k, 1≤k≤N} a(k)`.  For a compactly supported source
sampled on the ray `x,2x,...`, this is exactly `sum_m f(m*n*x)`. -/
def finiteApertureRaySum (N : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ (Finset.Icc 1 N).filter (n ∣ ·), a k

/-- Möbius reconstruction of the base value from all finite dilation tails. -/
def finiteApertureMobiusReconstruction (N : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) *
    finiteApertureRaySum N a n

/-- Exact finite Möbius inversion: the aperture dilation tails recover the base source value. -/
theorem finiteApertureMobiusReconstruction_eq {N : ℕ} (hN : 1 ≤ N) (a : ℕ → ℂ) :
    finiteApertureMobiusReconstruction N a = a 1 := by
  rw [finiteApertureMobiusReconstruction]
  calc
    (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ) *
        finiteApertureRaySum N a n) =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ k ∈ (Finset.Icc 1 N).filter (n ∣ ·),
            (ArithmeticFunction.moebius n : ℂ) * a k := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [finiteApertureRaySum, Finset.mul_sum]
    _ = ∑ k ∈ Finset.Icc 1 N,
          ∑ n ∈ k.divisors, (ArithmeticFunction.moebius n : ℂ) * a k := by
      symm
      rw [Finset.sum_comm']
      intro k n
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hk1, hkN⟩, hnk, _⟩
        exact ⟨⟨⟨hk1, hkN⟩, hnk⟩,
          Nat.pos_of_dvd_of_pos hnk (by omega),
          le_trans (Nat.le_of_dvd (by omega) hnk) hkN⟩
      · rintro ⟨⟨⟨hk1, hkN⟩, hnk⟩, _⟩
        exact ⟨⟨hk1, hkN⟩, hnk, by omega⟩
    _ = ∑ k ∈ Finset.Icc 1 N,
          (∑ n ∈ k.divisors, (ArithmeticFunction.moebius n : ℂ)) * a k := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
    _ = ∑ k ∈ Finset.Icc 1 N, (if k = 1 then 1 else 0) * a k := by
      apply Finset.sum_congr rfl
      intro k _hk
      congr 1
      rw [← Int.cast_sum, sum_moebius_divisors]
      split <;> simp
    _ = a 1 := by simp [hN]

/-- The finite ray energy whose continuum integral is the true aperture Hilbert metric. -/
def finiteApertureRayEnergy (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ‖finiteApertureRaySum N a n‖ ^ 2

theorem finiteApertureRayEnergy_nonneg (N : ℕ) (a : ℕ → ℂ) :
    0 ≤ finiteApertureRayEnergy N a := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Pointwise Hilbert coercivity forced by Möbius recovery.  Integrating this inequality along a
fixed source interval gives the paper's `lambda⁻¹` local frame floor. -/
theorem norm_base_sq_le_card_mul_finiteApertureRayEnergy
    {N : ℕ} (hN : 1 ≤ N) (a : ℕ → ℂ) :
    ‖a 1‖ ^ 2 ≤ ((Finset.Icc 1 N).card : ℝ) * finiteApertureRayEnergy N a := by
  have hnorm : ‖a 1‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ‖finiteApertureRaySum N a n‖ := by
    rw [← finiteApertureMobiusReconstruction_eq hN a]
    calc
      ‖finiteApertureMobiusReconstruction N a‖ ≤
          ∑ n ∈ Finset.Icc 1 N,
            ‖(ArithmeticFunction.moebius n : ℂ) * finiteApertureRaySum N a n‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖finiteApertureRaySum N a n‖ := by
        apply Finset.sum_le_sum
        intro n _hn
        rw [norm_mul]
        have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
        exact mul_le_of_le_one_left (norm_nonneg _) hmu
  have hsq : ‖a 1‖ ^ 2 ≤
      (∑ n ∈ Finset.Icc 1 N, ‖finiteApertureRaySum N a n‖) ^ 2 := by
    nlinarith [norm_nonneg (a 1),
      Finset.sum_nonneg (s := Finset.Icc 1 N)
        (fun n _ => norm_nonneg (finiteApertureRaySum N a n))]
  exact hsq.trans (by
    simpa [finiteApertureRayEnergy] using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.Icc 1 N) (f := fun n => ‖finiteApertureRaySum N a n‖)))

/-- The algebraic no-go closure: zero finite aperture ray energy forces the visible base source
value to vanish. -/
theorem finiteApertureRayEnergy_eq_zero_imp_base_eq_zero
    {N : ℕ} (hN : 1 ≤ N) {a : ℕ → ℂ}
    (henergy : finiteApertureRayEnergy N a = 0) : a 1 = 0 := by
  have h := norm_base_sq_le_card_mul_finiteApertureRayEnergy hN a
  rw [henergy, mul_zero] at h
  have : ‖a 1‖ = 0 := by nlinarith [norm_nonneg (a 1)]
  exact norm_eq_zero.mp this

end RHTower
