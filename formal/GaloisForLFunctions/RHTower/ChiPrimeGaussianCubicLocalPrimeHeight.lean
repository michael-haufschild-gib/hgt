import GaloisForLFunctions.RHTower.ChiRamanujanLabelledGridAction
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicPrimeHeight

/-!
# The actual cubic as a complete local prime-height inverse profile

Each full third labelled source selects its exact physical prime height.
Whole-block absolute summability justifies the finite local-grid exchange
with both remaining tangential lift sums. Both original physical exclusions
transfer to the distinguished labels, forcing the two complete local bases.
All complementary prime factors remain in the inverse profile, including its
zero axes and intersection. The unconditional actual Schwartz family keeps
the original sharp/smooth error. No growing signed saving or RH proof follows.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ContDiff BigOperators
namespace RHTower.BAGTrace

private lemma physical_phase (n : ℤ) (z : ℝ) :
    Complex.exp ((2*Real.pi*(n : ℝ)*z : ℝ)*Complex.I)=ramanujanFourierPhase n z := by
  unfold ramanujanFourierPhase
  congr 1
  push_cast
  ring

private lemma entry_physical {N : ℝ} (hN : 1 < N) (r : RamanujanBandPrime ⌊2*N⌋₊)
    {n : ℤ} (hn : n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋) :
    ramanujanDistinguishedPrimeEntry (Finset.range (⌊2*N⌋₊+1)) r.val n.natAbs =
      if n=(r.val : ℤ) then Real.log r.val else 0 := by
  have hnr : (n : ℝ) ∈ Icc N (2*N) := by
    simpa only [Finset.mem_Icc,Int.ceil_le,Int.le_floor,Set.mem_Icc] using hn
  have hn0 : 0 ≤ n := by exact_mod_cast (le_trans (by linarith : (0 : ℝ) ≤ N) hnr.1)
  have heZ : (n.natAbs : ℤ)=n := by rw [Int.natCast_natAbs,abs_of_nonneg hn0]
  have heR : (n.natAbs : ℝ)=(n : ℝ) := by
    calc
      (n.natAbs : ℝ) = ((n.natAbs : ℤ) : ℝ) := by rw [Int.cast_natCast]
      _ = (n : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) heZ
  have hb : n.natAbs ∈ Finset.Icc 2 ⌊2*N⌋₊ := by
    refine Finset.mem_Icc.mpr ⟨?_,Nat.le_floor (heR ▸ hnr.2)⟩
    have h : (1 : ℝ)<(n.natAbs : ℝ) := by rw [heR]; exact hN.trans_le hnr.1
    have : 1 < n.natAbs := by exact_mod_cast h
    omega
  have he : n.natAbs=r.val ↔ n=(r.val : ℤ) := by
    constructor
    · intro h
      rw [← heZ,h]
    · intro h
      simp only [h,Int.natAbs_natCast]
  exact (ramanujanDistinguishedPrimeEntry_band ⌊2*N⌋₊ r ⟨n.natAbs,hb⟩).trans (by simp only [he])

/-- One full labelled third grid selects exactly its own physical prime height. -/
theorem bagLabelledThirdGrid_block {N : ℝ} (hN : 1 < N)
    (r : RamanujanBandPrime ⌊2*N⌋₊) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc N (2*N) → f v=0)
    (ξ υ : ℝ) :
    (∑ t : RamanujanLocalGrid (Finset.range (⌊2*N⌋₊+1)),
      (ramanujanLabelledLocalGridWeight r t : ℂ)*
        bagThirdLiftBlock f ξ υ (ramanujanLocalGridNode t)) =
      (Real.log r.val : ℂ)*bagThirdPhysicalSlice f ξ υ (r.val : ℝ) := by
  classical
  have he (z : ℝ) : bagThirdLiftBlock f ξ υ z =
      ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
        ramanujanFourierPhase n z*bagThirdPhysicalSlice f ξ υ n := by
    simpa only [bagThirdLiftBlock,physical_phase] using
      bagThirdLift_poisson_finite f N (2*N) hs ξ υ z
  simp_rw [he]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  trans ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
    (ramanujanDistinguishedPrimeEntry (Finset.range (⌊2*N⌋₊+1)) r.val n.natAbs : ℂ)*
      bagThirdPhysicalSlice f ξ υ n
  · apply Finset.sum_congr rfl
    intro n hn
    rw [← ramanujanLabelledLocalGridWeight_fourier]
    simp only [Finset.sum_mul,mul_assoc]
  trans ∑ n ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋,
    if n=(r.val : ℤ) then (Real.log r.val : ℂ)*bagThirdPhysicalSlice f ξ υ (r.val : ℝ) else 0
  · apply Finset.sum_congr rfl
    intro n hn
    rw [entry_physical hN r hn]
    split_ifs with h
    · simp only [h,Int.cast_natCast]
    · simp only [Complex.ofReal_zero,zero_mul]
  rw [Finset.sum_ite_eq']
  by_cases hr : (r.val : ℤ) ∈ Finset.Icc (⌈N⌉ : ℤ) ⌊2*N⌋
  · rw [if_pos hr]
  · rw [if_neg hr]
    have hro : (r.val : ℝ) ∉ Icc N (2*N) := by
      simpa only [Finset.mem_Icc,Int.ceil_le,Int.le_floor,Int.cast_natCast,Set.mem_Icc] using hr
    rw [bagThirdPhysicalSlice_zero f N (2*N) hs ξ υ (r.val : ℝ) hro,mul_zero]

private lemma sum_tsum_tsum {ι : Type*} [Fintype ι] (H : ι → ℤ → ℤ → ℂ)
    (hinner : ∀ i k, Summable (H i k)) (houter : ∀ i, Summable (fun k => ∑' l, H i k l)) :
    (∑ i, ∑' k, ∑' l, H i k l) = ∑' k, ∑' l, ∑ i, H i k l := by
  rw [← Summable.tsum_finsetSum (fun i _ => houter i)]
  apply tsum_congr
  intro k
  exact (Summable.tsum_finsetSum (fun i _ => hinner i k)).symm

/-- The exact height selection holds with both entire tangential lift sums. -/
theorem bagLabelledThirdGrid_lifted {N : ℝ} (hN : 1 < N)
    (r : RamanujanBandPrime ⌊2*N⌋₊) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc N (2*N) → f v=0)
    (x y : ℝ) :
    (∑ t : RamanujanLocalGrid (Finset.range (⌊2*N⌋₊+1)),
      (ramanujanLabelledLocalGridWeight r t : ℂ)*
        bagLiftedFourierTest f (x,y,ramanujanLocalGridNode t)) =
      (Real.log r.val : ℂ)*bagPhysicalHeightTest f (r.val : ℤ) (x,y,0) := by
  simp_rw [bagLiftedFourierTest_eq_thirdBlocks]
  simp only [← tsum_mul_left]
  rw [sum_tsum_tsum _ (fun t k =>
    ((summable_bagThirdLiftBlocks f x y (ramanujanLocalGridNode t)).1 k).mul_left _)
      (fun t => ?_)]
  · simp only [bagLabelledThirdGrid_block hN r f hs,tsum_mul_left,
      bagPhysicalHeightTest,ramanujanFourierPhase,Int.cast_natCast,mul_zero,zero_mul,
      Complex.ofReal_zero,Complex.exp_zero,one_mul]
  · simpa only [tsum_mul_left] using
      ((summable_bagThirdLiftBlocks f x y (ramanujanLocalGridNode t)).2).mul_left
        (ramanujanLabelledLocalGridWeight r t : ℂ)

/-- Complete literal tensor at one labelled height; all complementary factors remain. -/
theorem bagExcludedLocalTripleAction_lifted {N : ℝ} (hN : 1 < N)
    (r : RamanujanBandPrime ⌊2*N⌋₊) (f : SchwartzMap BAGPhysicalSpace ℂ)
    (hs : ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc N (2*N) → f v=0) :
    ramanujanExcludedLocalTripleAction r (bagLiftedFourierTest f) =
      (Real.log r.val : ℂ)*ramanujanExcludedLocalPairAction r (bagPhysicalHeightTest f (r.val : ℤ)) := by
  unfold ramanujanExcludedLocalTripleAction ramanujanExcludedLocalPairAction
  simp only [bagLabelledThirdGrid_lifted hN r f hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- All prime-height inverse profiles, with both masks and every local cofactor retained. -/
def bagLocalPrimeHeightInverseAction (N : ℝ) (f : SchwartzMap BAGPhysicalSpace ℂ) : ℂ :=
  ∑ r : RamanujanBandPrime ⌊2*N⌋₊, (Real.log r.val : ℂ)*
    ramanujanExcludedInverseProfileAction r (bagPhysicalHeightTest f (r.val : ℤ))

private lemma actual_box {N : ℝ} {η : ℝ → ℝ}
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v) :
    ∀ v : BAGPhysicalSpace, ∀ i : Fin 3, v i ∉ Icc N (2*N) → A v=0 := by
  intro v i hi
  have hz0 : η (v i)=0 := hz _ (fun h => hi ⟨h.1.le,h.2.le⟩)
  rw [hA]
  fin_cases i <;> simp_all [bagCubicPhysicalAmplitude,bagCubicMellinSliceValue]

/-- The actual complete smoothed cubic equals the full all-prime inverse-profile action. -/
theorem primeGaussianCubicSmoothedOffDiagonal_eq_localPrimeHeight {N : ℝ} (hN : 1 < N)
    {η : ℝ → ℝ} (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (A : SchwartzMap BAGPhysicalSpace ℂ) (hA : ∀ v, A v=bagCubicPhysicalAmplitude N η v) :
    primeGaussianCubicSmoothedOffDiagonal N η=bagLocalPrimeHeightInverseAction N A := by
  have hbox := actual_box hz A hA
  have hf : 1 ≤ ⌊N⌋₊ := by simpa using Nat.floor_mono hN.le
  have hS : ∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊, 1 < n ∧ n ≤ ⌊2*N⌋₊ := by
    intro n hn
    exact ⟨lt_of_le_of_lt hf (Finset.mem_Ioc.mp hn).1,(Finset.mem_Ioc.mp hn).2⟩
  rw [primeGaussianCubicSmoothedOffDiagonal_eq_liftedAction hN.le hz A hA]
  rw [bagLiftedFourierTest_eq_finite (by linarith : 0 ≤ N) hz A hA]
  rw [ramanujanCriticalTripleAtomAction_eq_excludedLocal _ _ hS]
  rw [← bagLiftedFourierTest_eq_finite (by linarith : 0 ≤ N) hz A hA]
  unfold bagLocalPrimeHeightInverseAction
  apply Finset.sum_congr rfl
  intro r hr
  rw [bagExcludedLocalTripleAction_lifted hN r A hbox,ramanujanExcludedLocalPairAction_inverse]

/-- Unconditional actual family with the original normalized sharp/smooth error. -/
theorem exists_bagLocalPrimeHeightInverseFamily :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        primeGaussianCubicSmoothedOffDiagonal N (η N)=bagLocalPrimeHeightInverseAction N (A N)) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal N-bagLocalPrimeHeightInverseAction N (A N)‖) atTop (𝓝 0) := by
  obtain ⟨η,A,hA,herr⟩ := exists_bagCubicPhysicalFourierFamily
  have he : ∀ᶠ N : ℕ in atTop,
      primeGaussianCubicSmoothedOffDiagonal N (η N)=bagLocalPrimeHeightInverseAction N (A N) := by
    filter_upwards [hA,eventually_ge_atTop (2 : ℕ)] with N hreg hN
    exact primeGaussianCubicSmoothedOffDiagonal_eq_localPrimeHeight
      (by exact_mod_cast (by omega : 1 < N)) hreg.2.2.2.1 (A N) hreg.2.2.2.2.2.1
  refine ⟨η,A,?_,?_⟩
  · filter_upwards [hA,he] with N hreg heq
    exact ⟨hreg.1,hreg.2.1,hreg.2.2.1,hreg.2.2.2.1,hreg.2.2.2.2.1,hreg.2.2.2.2.2.1,heq⟩
  · apply herr.congr'
    filter_upwards [he] with N heq
    rw [heq]

end RHTower.BAGTrace
