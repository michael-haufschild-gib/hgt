import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRobustIndexOfTheFiniteComb

/-!
# Gram matrices of sampled comb forms

Real polarization gives the complex Gram of a finite coefficient family.
Adding a mass margin before polarization makes its negative index a lower
bound for the robust index of the literal comb.
-/

noncomputable section

open Finset Filter Topology Matrix MeasureTheory Zeta23

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open HTGeometry AbsoluteGeometryOfSpecZ ArithmeticIndexDescent ArithmeticCastelnuovoSeveri

/-- Hermitian extension of the real polar entries of a quadratic form. -/
def realPolarGram {α : Type*} {n : ℕ} (q : (α → ℝ) → ℝ) (v : Fin n → α → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (((q (v i) + q (v j) - q (fun u => v j u - v i u)) / 2 : ℝ) : ℂ)

theorem hermQuad_realPolarGram {α : Type*} {n : ℕ} {q : (α → ℝ) → ℝ}
    {v : Fin n → α → ℝ} (hq : PolarOn q v univ) (c : Fin n → ℂ) :
    hermQuad (realPolarGram q v) c =
      q (fun u => ∑ i, (c i).re * v i u) + q (fun u => ∑ i, (c i).im * v i u) := by
  rw [hq (fun i => (c i).re), hq (fun i => (c i).im)]
  simp only [realPolarGram, hermQuad, dotProduct, mulVec, Finset.mul_sum, Complex.re_sum,
    Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, zero_add, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Coefficient mass as a quadratic form on real divisors. -/
def combMass (S : Finset ℕ) (c : ℕ → ℝ) : ℝ := ∑ n ∈ S, c n ^ 2

theorem polarOn_combMass {n : ℕ} (S : Finset ℕ) (v : Fin n → ℕ → ℝ) :
    PolarOn (combMass S) v univ := by
  have h := polarOn_of_biadditive (fun c d : ℕ → ℝ => ∑ i ∈ S, c i * d i)
    (fun c d e => by simp only [add_mul, Finset.sum_add_distrib])
    (fun t c e => by simp only [mul_assoc, Finset.mul_sum])
    (fun c d e => by simp only [mul_add, Finset.sum_add_distrib])
    (fun t c e => by simp only [Finset.mul_sum]; congr 1; ext i; ring)
    v univ
  change PolarOn (fun c => ∑ i ∈ S, c i ^ 2) v univ
  simpa only [pow_two] using h

/-- The comb form shifted by its fixed coefficient-mass margin. -/
def shiftedCombForm (S : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) : ℝ :=
  combForm S c + η * combMass S c

theorem polarOn_shiftedCombForm {n : ℕ} (S : Finset ℕ) (η : ℝ) (v : Fin n → ℕ → ℝ) :
    PolarOn (shiftedCombForm S η) v univ :=
  (polarOn_combForm S v univ).add ((polarOn_combMass S v).const_mul η)

/-- A finite real divisor family, tested with complex coefficients. -/
def combCombination {n : ℕ} (S : Finset ℕ) (v : Fin n → ℕ → ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (S → ℂ) where
  toFun c j := ∑ i, c i * (v i j : ℂ)
  map_add' c d := by ext j; simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by ext j; simp [Finset.mul_sum, mul_assoc]

/-- Every negative square in a finite sampled family survives in the
robust index of the whole comb. -/
theorem shiftedCombGram_negIndex_le {n : ℕ} (S : Finset ℕ) (η : ℝ) (v : Fin n → ℕ → ℝ) :
    (hermNegIndex (realPolarGram (shiftedCombForm S η) v) : ℕ∞) ≤ robustCombIndex S η := by
  apply hermNegIndex_le_robustCombIndex _ (combCombination S v)
  intro c
  rw [hermQuad_realPolarGram (polarOn_shiftedCombForm S η v)]
  have hre : ∀ j ∈ S, (combExtension S (combCombination S v c) j).re =
      ∑ i, (c i).re * v i j := by
    intro j hj
    simp [combExtension, combCombination, hj, Complex.mul_re]
  have him : ∀ j ∈ S, (combExtension S (combCombination S v c) j).im =
      ∑ i, (c i).im * v i j := by
    intro j hj
    simp [combExtension, combCombination, hj, Complex.mul_im]
  rw [← combExtension_mass S (combCombination S v c)]
  unfold complexCombForm shiftedCombForm combMass
  rw [combForm_congr hre, combForm_congr him]
  rw [Finset.sum_congr rfl (fun j hj => congrArg (fun t : ℝ => t ^ 2) (hre j hj)),
    Finset.sum_congr rfl (fun j hj => congrArg (fun t : ℝ => t ^ 2) (him j hj))]
  ring

/-- Limiting mass of samples on the fixed comb window. -/
def packetWindowMass (K : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2

def shiftedPacketForm (K : ℕ) (η : ℝ) (f : ℝ → ℝ) : ℝ :=
  zeroSum f + η * packetWindowMass K f

theorem tendsto_shiftedCombForm_sample {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 1 ≤ K)
    (hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) (η : ℝ) :
    Tendsto (fun N : ℕ => shiftedCombForm (Ioc N (N + 3 * K * N)) η (sampleCoord f N))
      atTop (𝓝 (shiftedPacketForm K η f)) :=
  (tendsto_combForm_sample hf hfc hK hs).add
    ((tendsto_sum_sq_sampleCoord hf.continuous hK).const_mul η)

/-- Every mixed entry, including its mass margin, converges on one window. -/
theorem tendsto_shiftedCombGram_sample {n : ℕ} (f : Fin n → realTests)
    {K : ℕ} (hK : 1 ≤ K)
    (hs : ∀ i u, u ≤ Real.log 3 ∨ Real.log K ≤ u → (f i).1 u = 0)
    (η : ℝ) (i j : Fin n) :
    Tendsto (fun N : ℕ => realPolarGram (shiftedCombForm (Ioc N (N + 3 * K * N)) η)
      (fun k => sampleCoord (f k).1 N) i j) atTop
      (𝓝 (realPolarGram (shiftedPacketForm K η) (fun k => (f k).1) i j)) := by
  have hi := tendsto_shiftedCombForm_sample (f i).2.1 (f i).2.2 hK (hs i) η
  have hj := tendsto_shiftedCombForm_sample (f j).2.1 (f j).2.2 hK (hs j) η
  have hsub : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → (f j - f i).1 u = 0 := by
    intro u hu
    change (f j).1 u - (f i).1 u = 0
    rw [hs j u hu, hs i u hu, sub_self]
  have hd := tendsto_shiftedCombForm_sample (f j - f i).2.1 (f j - f i).2.2 hK hsub η
  have ht := (Complex.continuous_ofReal.tendsto _).comp (((hi.add hj).sub hd).div_const 2)
  refine ht.congr' (Eventually.of_forall fun N => ?_)
  change (((_ + _ - shiftedCombForm _ η (sampleCoord (f j - f i).1 N)) / 2 : ℝ) : ℂ) = _
  have he : sampleCoord (f j - f i).1 N =
      fun u => sampleCoord (f j).1 N u - sampleCoord (f i).1 N u := by
    funext u
    exact sub_div _ _ _
  rw [he]
  rfl

private theorem zeroSum_realTest (f : realTests) : zeroSum f.1 = realWeilForm f f := by
  rw [zeroSum_eq_weilFullFunctional f.2.1 f.2.2]
  rfl

/-- The zero-side polar Gram is the literal full Weil Gram. -/
theorem realPolarGram_zeroSum {n : ℕ} (f : Fin n → realTests) :
    realPolarGram zeroSum (fun i => (f i).1) = complexWeilMixed f f := by
  ext i j
  change (((zeroSum (f i).1 + zeroSum (f j).1 - zeroSum (f j - f i).1) / 2 : ℝ) : ℂ) = _
  rw [zeroSum_realTest, zeroSum_realTest, zeroSum_realTest]
  change (((_ + _ - _) / 2 : ℝ) : ℂ) = (realWeilForm (f i) (f j) : ℂ)
  apply congrArg Complex.ofReal
  simp only [map_sub, LinearMap.sub_apply]
  rw [realWeilForm_symm (f j) (f i)]
  ring

/-- A sufficiently small fixed mass margin preserves every negative square
of a finite packet family. -/
theorem exists_positive_margin_packet_index {n : ℕ} (f : Fin n → realTests) (K : ℕ) :
    ∃ η : ℝ, 0 < η ∧ hermNegIndex (complexWeilMixed f f) ≤
      hermNegIndex (realPolarGram (shiftedPacketForm K η) (fun i => (f i).1)) := by
  have hconv : ∀ i j, Tendsto (fun k : ℕ =>
      realPolarGram (shiftedPacketForm K (1 / ((k : ℝ) + 1))) (fun i => (f i).1) i j)
      atTop (𝓝 (complexWeilMixed f f i j)) := by
    intro i j
    rw [← realPolarGram_zeroSum f]
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have ht (g : ℝ → ℝ) : Tendsto (fun k : ℕ =>
        shiftedPacketForm K (1 / ((k : ℝ) + 1)) g) atTop (𝓝 (zeroSum g)) := by
      simpa only [shiftedPacketForm, zero_mul, add_zero] using
        tendsto_const_nhds.add (hz.mul_const (packetWindowMass K g))
    exact (Complex.continuous_ofReal.tendsto _).comp
      ((((ht (f i).1).add (ht (f j).1)).sub (ht (fun u => (f j).1 u - (f i).1 u))).div_const 2)
  obtain ⟨k, hk⟩ := (eventually_negIndex_limit_le
    (fun k : ℕ => realPolarGram (shiftedPacketForm K (1 / ((k : ℝ) + 1)))
      (fun i => (f i).1)) (complexWeilMixed f f) hconv).exists
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

/-- A common sampling window captures every negative square of its finite
packet family with one fixed positive margin at every sufficiently large scale. -/
theorem exists_margin_eventually_packet_index_le_robustCombIndex {n : ℕ}
    (f : Fin n → realTests) {K : ℕ} (hK : 1 ≤ K)
    (hs : ∀ i u, u ≤ Real.log 3 ∨ Real.log K ≤ u → (f i).1 u = 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop,
      (hermNegIndex (complexWeilMixed f f) : ℕ∞) ≤
        robustCombIndex (Ioc N (N + 3 * K * N)) η := by
  obtain ⟨η, hη, hindex⟩ := exists_positive_margin_packet_index f K
  refine ⟨η, hη, ?_⟩
  have hev := eventually_negIndex_limit_le
    (fun N : ℕ => realPolarGram (shiftedCombForm (Ioc N (N + 3 * K * N)) η)
      (fun k => sampleCoord (f k).1 N))
    (realPolarGram (shiftedPacketForm K η) (fun k => (f k).1))
    (tendsto_shiftedCombGram_sample f hK hs η)
  filter_upwards [hev] with N hN
  exact (ENat.coe_le_coe.mpr (hindex.trans hN)).trans
    (shiftedCombGram_negIndex_le _ η (fun k => sampleCoord (f k).1 N))

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
