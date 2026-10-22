import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiFiniteUpperKernelInertia
import GaloisForLFunctions.HTGeometry.PoleLocalizedExactNegativeSquares
import GaloisForLFunctions.HTGeometry.NevCombinationDiscrete

open Complex Set Topology Filter Matrix
open scoped ComplexConjugate ComplexOrder BigOperators
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Every fiber of the shifted upper-pole coordinate contains only finitely many divisor copies. -/
theorem finite_xiShiftPoleCoordinate_fiber (omega : ℝ) (z : ℂ) :
    {q : XiShiftRightZeroCopy omega | xiShiftPoleCoordinate omega q = z}.Finite := by
  let alpha : ℂ := -z - (omega : ℂ) * I
  have hpre :
      {q : XiShiftRightZeroCopy omega | xiSpectralPoint q.1 = alpha}.Finite := by
    have hbase := finite_xiSpectralPoint_fiber alpha
    exact hbase.preimage (fun _ _ _ _ h => Subtype.ext h)
  apply hpre.subset
  intro q hq
  change xiSpectralPoint q.1 = alpha
  change -xiSpectralPoint q.1 - (omega : ℂ) * I = z at hq
  dsimp only [alpha]
  linear_combination -hq

/-- An infinite shifted divisor-copy type has infinitely many distinct upper-pole coordinates. -/
theorem xiShiftPoleCoordinate_range_infinite (omega : ℝ)
    [Infinite (XiShiftRightZeroCopy omega)] :
    (Set.range (xiShiftPoleCoordinate omega)).Infinite := by
  intro hrange
  have huniv : (Set.univ : Set (XiShiftRightZeroCopy omega)).Finite := by
    have hunion : (Set.univ : Set (XiShiftRightZeroCopy omega)) =
        ⋃ z ∈ Set.range (xiShiftPoleCoordinate omega),
          {q | xiShiftPoleCoordinate omega q = z} := by
      ext q
      constructor
      · intro _
        refine Set.mem_iUnion.2 ⟨xiShiftPoleCoordinate omega q, ?_⟩
        refine Set.mem_iUnion.2 ⟨⟨q, rfl⟩, ?_⟩
        rfl
      · intro _
        trivial
    rw [hunion]
    exact hrange.biUnion fun z _ => finite_xiShiftPoleCoordinate_fiber omega z
  letI : Finite (XiShiftRightZeroCopy omega) := Set.finite_univ_iff.mp huniv
  exact not_finite (XiShiftRightZeroCopy omega)

/-- Every finite size occurs as a packet of shifted divisor copies with distinct pole coordinates. -/
theorem exists_xiShiftPoleCoordinate_injective_packet (omega : ℝ)
    [Infinite (XiShiftRightZeroCopy omega)] (r : ℕ) :
    ∃ q : Fin r → XiShiftRightZeroCopy omega,
      Function.Injective (fun i => xiShiftPoleCoordinate omega (q i)) := by
  let e : ℕ ↪ {z // z ∈ Set.range (xiShiftPoleCoordinate omega)} :=
    (xiShiftPoleCoordinate_range_infinite omega).natEmbedding
  let q : Fin r → XiShiftRightZeroCopy omega := fun i =>
    Classical.choose (e (i : ℕ)).property
  have hq : ∀ i, xiShiftPoleCoordinate omega (q i) = (e (i : ℕ)).1 := fun i =>
    Classical.choose_spec (e (i : ℕ)).property
  refine ⟨q, ?_⟩
  intro i j hij
  change xiShiftPoleCoordinate omega (q i) =
    xiShiftPoleCoordinate omega (q j) at hij
  have hval : (e (i : ℕ)).1 = (e (j : ℕ)).1 := by
    exact (hq i).symm.trans (hij.trans (hq j))
  have heq : e (i : ℕ) = e (j : ℕ) := by
    exact Subtype.ext hval
  exact Fin.ext (e.injective heq)

/-- A negative-definite sampled transpose matrix gives a literal finite kernel-negative packet. -/
theorem hasFiniteKernelNegativeDimension_of_sampleTranspose_negDef
    {X : Type*} {r : ℕ} (K : X → X → ℂ) (w : Fin r → X)
    (hneg : ∀ c : Fin r → ℂ, c ≠ 0 →
      (star c ⬝ᵥ
        (Matrix.of fun i j => K (w j) (w i)).mulVec c).re < 0) :
    HasFiniteKernelNegativeDimension K r := by
  classical
  let d : Fin r → X →₀ ℂ := fun i =>
    Finsupp.mapDomain w (Finsupp.single i 1)
  refine ⟨d, fun c hc => ?_⟩
  let cf : Fin r →₀ ℂ :=
    (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin r)).symm c
  have hcf : ∀ i, cf i = c i := by
    intro i
    have h := congrFun
      ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin r)).apply_symm_apply c) i
    exact h
  have hsingle : ∑ i, c i • Finsupp.single i (1 : ℂ) = cf := by
    let L := Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin r)
    have hbasis : ∀ j : Fin r,
        L (Finsupp.single j (1 : ℂ)) = Pi.single j 1 := by
      intro j
      ext i
      change (Finsupp.single j (1 : ℂ)) i =
        (Pi.single j (1 : ℂ) : Fin r → ℂ) i
      by_cases h : i = j
      · simp [h]
      · simp [h]
    apply L.injective
    rw [map_sum]
    simp_rw [map_smul, hbasis]
    change (∑ j, c j • Pi.single j (1 : ℂ)) = c
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne (Ne.symm hji)]
      simp
    · exact fun h => (h (Finset.mem_univ i)).elim
  have hsum : ∑ i, c i • d i = Finsupp.mapDomain w cf := by
    simp only [d, ← Finsupp.mapDomain_smul]
    calc
      ∑ i, Finsupp.mapDomain w (c i • Finsupp.single i (1 : ℂ)) =
          Finsupp.mapDomain w (∑ i, c i • Finsupp.single i (1 : ℂ)) := by
        exact (map_sum (Finsupp.mapDomain.addMonoidHom w)
          (fun i => c i • Finsupp.single i (1 : ℂ)) Finset.univ).symm
      _ = Finsupp.mapDomain w cf := by rw [hsingle]
  rw [hsum, kernelForm_mapDomain, kernelForm]
  rw [Finsupp.sum_fintype]
  · have hinner : ∀ i : Fin r,
        cf.sum (fun x b => (starRingEnd ℂ) (cf i) * b * K (w x) (w i)) =
          ∑ j : Fin r, (starRingEnd ℂ) (cf i) * cf j * K (w j) (w i) := by
      intro i
      rw [Finsupp.sum_fintype]
      intro j
      simp only [mul_zero, zero_mul]
    simp_rw [hinner]
    simp_rw [hcf]
    have hquad :
        (∑ i : Fin r, ∑ j : Fin r,
          (starRingEnd ℂ) (c i) * c j * K (w j) (w i)) =
          star c ⬝ᵥ (Matrix.of fun i j => K (w j) (w i)).mulVec c := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply,
        Pi.star_apply, RCLike.star_def]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hquad]
    exact hneg c hc
  · intro i
    simp only [map_zero, zero_mul, Finsupp.sum_fun_zero]

/-- Denominator-cleared literal shifted-Xi Hermite--Biehler kernel. -/
def xiShiftClearedUpperKernel (omega : ℝ) (z w : ℂ) : ℂ :=
  I / (z - (starRingEnd ℂ) w) *
    (suzukiCanonicalE omega z *
        (starRingEnd ℂ) (suzukiCanonicalE omega w) -
      suzukiCanonicalE omega (-z) *
        (starRingEnd ℂ) (suzukiCanonicalE omega (-w)))

/-- Clearing the denominator is an exact diagonal congruence on the regular upper locus. -/
theorem xiShiftClearedUpperKernel_eq_regular_congruence
    (omega : ℝ) (z w : XiShiftRegularUpperNode omega) :
    xiShiftClearedUpperKernel omega z.1 w.1 =
      suzukiCanonicalE omega z.1 *
        xiShiftRegularUpperKernel omega z w *
        (starRingEnd ℂ) (suzukiCanonicalE omega w.1) := by
  have hzw := upperHalfPlane_sub_conj_ne_zero z.property.1 w.property.1
  rw [xiShiftClearedUpperKernel, xiShiftRegularUpperKernel,
    upperHalfPlaneSchurKernel, suzukiCanonicalTheta_eq_E_neg_div_E,
    suzukiCanonicalTheta_eq_E_neg_div_E]
  simp only [map_div₀]
  field_simp [z.property.2, w.property.2,
    (map_ne_zero (starRingEnd ℂ)).mpr w.property.2, hzw]

/-- At a nonexceptional shifted pole, normalized cleared kernel is the negative Hardy Cauchy
kernel. -/
theorem xiShiftClearedUpperKernel_normalized_poles
    {omega : ℝ} (hnon : SuzukiShiftNonexceptional omega)
    (q r : XiShiftRightZeroCopy omega) :
    (suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q))⁻¹ *
        xiShiftClearedUpperKernel omega
          (xiShiftPoleCoordinate omega q) (xiShiftPoleCoordinate omega r) *
        (starRingEnd ℂ)
          ((suzukiCanonicalE omega (-xiShiftPoleCoordinate omega r))⁻¹) =
      -I / (xiShiftPoleCoordinate omega q -
        (starRingEnd ℂ) (xiShiftPoleCoordinate omega r)) := by
  have hden := upperHalfPlane_sub_conj_ne_zero
    (xiShiftPoleCoordinate_im_pos omega q)
    (xiShiftPoleCoordinate_im_pos omega r)
  rw [xiShiftClearedUpperKernel,
    suzukiCanonicalE_xiShiftPoleCoordinate_eq_zero,
    suzukiCanonicalE_xiShiftPoleCoordinate_eq_zero]
  simp only [map_zero, mul_zero, zero_sub, map_inv₀]
  field_simp [hnon q, hnon r, (map_ne_zero (starRingEnd ℂ)).mpr (hnon r), hden]

/-- Cleared kernel entries along vertical pole approaches converge to their pole values. -/
theorem tendsto_xiShiftClearedUpperKernel_poleApproach
    {r : ℕ} (omega : ℝ) (t : Fin r → ℂ)
    (ht : ∀ i, 0 < (t i).im) (i j : Fin r) :
    Tendsto
      (fun y : ℝ => xiShiftClearedUpperKernel omega
        (poleApproachNode t y i) (poleApproachNode t y j))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (xiShiftClearedUpperKernel omega (t i) (t j))) := by
  have hden : t i - (starRingEnd ℂ) (t j) ≠ 0 :=
    upperHalfPlane_sub_conj_ne_zero (ht i) (ht j)
  let zi : ℝ → ℂ := fun y => poleApproachNode t y i
  let zj : ℝ → ℂ := fun y => poleApproachNode t y j
  have hzi : Continuous zi := by
    exact continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)
  have hzj : Continuous zj := by
    exact continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)
  have hconj : Continuous (fun z : ℂ => (starRingEnd ℂ) z) :=
    Complex.continuous_conj
  have hE : Continuous (suzukiCanonicalE omega) :=
    (differentiable_suzukiCanonicalE omega).continuous
  have hdenCont : ContinuousAt
      (fun y => zi y - (starRingEnd ℂ) (zj y)) 0 :=
    hzi.continuousAt.sub (hconj.comp hzj).continuousAt
  have hden0 : zi 0 - (starRingEnd ℂ) (zj 0) ≠ 0 := by
    simpa [zi, zj, poleApproachNode] using hden
  have hnumCont : ContinuousAt
      (fun y =>
        suzukiCanonicalE omega (zi y) *
            (starRingEnd ℂ) (suzukiCanonicalE omega (zj y)) -
          suzukiCanonicalE omega (-zi y) *
            (starRingEnd ℂ) (suzukiCanonicalE omega (-zj y))) 0 := by
    exact
      ((hE.comp hzi).continuousAt.mul
        (hconj.comp (hE.comp hzj)).continuousAt).sub
      ((hE.comp hzi.neg).continuousAt.mul
        (hconj.comp (hE.comp hzj.neg)).continuousAt)
  have hcont : ContinuousAt
      (fun y : ℝ => xiShiftClearedUpperKernel omega
        (poleApproachNode t y i) (poleApproachNode t y j)) 0 := by
    change ContinuousAt (fun y =>
      I / (zi y - (starRingEnd ℂ) (zj y)) *
        (suzukiCanonicalE omega (zi y) *
            (starRingEnd ℂ) (suzukiCanonicalE omega (zj y)) -
          suzukiCanonicalE omega (-zi y) *
            (starRingEnd ℂ) (suzukiCanonicalE omega (-zj y)))) 0
    exact (continuousAt_const.div hdenCont hden0).mul hnumCont
  have hzero :
      xiShiftClearedUpperKernel omega
          (poleApproachNode t 0 i) (poleApproachNode t 0 j) =
        xiShiftClearedUpperKernel omega (t i) (t j) := by
    simp [poleApproachNode]
  rw [← hzero]
  exact hcont.tendsto.mono_left inf_le_left

/-- Vertical approaches to finitely many distinct shifted poles eventually lie in the literal
regular locus. -/
theorem eventually_suzukiCanonicalE_ne_zero_poleApproach
    {r : ℕ} (omega : ℝ) (t : Fin r → ℂ)
    (htinj : Function.Injective t) :
    ∀ᶠ y : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ i, suzukiCanonicalE omega (poleApproachNode t y i) ≠ 0 := by
  rw [Filter.eventually_all]
  intro i
  have havoid := eventually_poleApproachNode_avoids_poles t htinj
  have hpunct : Tendsto (fun y : ℝ => poleApproachNode t y i)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝[≠] (t i)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_poleApproachNode t i, ?_⟩
    filter_upwards [havoid] with y hy
    exact hy i i
  exact hpunct.eventually
    (HTGeometry.eventually_ne_zero_of_entire
      (differentiable_suzukiCanonicalE omega)
      (z₁ := 0) (suzukiCanonicalE_zero_ne_zero omega) (t i))

/-- An infinite strict-right shifted-Xi divisor forces unbounded negative dimension of the literal
regular upper-half-plane kernel. -/
theorem xiShiftRegularUpperKernel_hasNegativeDimension_infinite
    {omega : ℝ} [Infinite (XiShiftRightZeroCopy omega)]
    (hnon : SuzukiShiftNonexceptional omega) (r : ℕ) :
    HasFiniteKernelNegativeDimension (xiShiftRegularUpperKernel omega) r := by
  classical
  obtain ⟨q, hqinj⟩ :=
    exists_xiShiftPoleCoordinate_injective_packet omega r
  let t : Fin r → ℂ := fun i => xiShiftPoleCoordinate omega (q i)
  have ht : ∀ i, 0 < (t i).im := fun i =>
    xiShiftPoleCoordinate_im_pos omega (q i)
  have htinj : Function.Injective t := hqinj
  let a : Fin r → ℂ := fun i =>
    (suzukiCanonicalE omega (-t i))⁻¹
  have ha : ∀ i, a i ≠ 0 := fun i => by
    exact inv_ne_zero (hnon (q i))
  let G : ℝ → Matrix (Fin r) (Fin r) ℂ := fun y i j =>
    a j * xiShiftClearedUpperKernel omega
      (poleApproachNode t y j) (poleApproachNode t y i) *
      (starRingEnd ℂ) (a i)
  let G₀ : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i j =>
    -I / (t j - (starRingEnd ℂ) (t i))
  have hG₀eq : G₀ =
      (1 / 2 : ℝ) • (upperPoleLocalizationLimit t).transpose := by
    ext i j
    simp only [G₀, Matrix.of_apply, Matrix.smul_apply,
      Matrix.transpose_apply, upperPoleLocalizationLimit, Complex.real_smul]
    norm_num
    ring
  have hG₀neg : (-G₀).PosDef := by
    have hbase := (upperPoleLocalizationLimit_neg_posDef t ht htinj).transpose
    have hscaled := hbase.smul (by norm_num : (0 : ℝ) < 1 / 2)
    have heq : -G₀ =
        (1 / 2 : ℝ) • (-upperPoleLocalizationLimit t).transpose := by
      rw [hG₀eq]
      ext i j
      simp
    rw [heq]
    exact hscaled
  have hconv : ∀ i j,
      Tendsto (fun y => G y i j)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (G₀ i j)) := by
    intro i j
    have hk := tendsto_xiShiftClearedUpperKernel_poleApproach
      omega t ht j i
    have hleft : Tendsto (fun _ : ℝ => a j)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (a j)) := tendsto_const_nhds
    have hright : Tendsto (fun _ : ℝ => (starRingEnd ℂ) (a i))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ((starRingEnd ℂ) (a i))) := tendsto_const_nhds
    have hmul := (hleft.mul hk).mul hright
    have hpole := xiShiftClearedUpperKernel_normalized_poles
      hnon (q j) (q i)
    change a j * xiShiftClearedUpperKernel omega (t j) (t i) *
        (starRingEnd ℂ) (a i) = G₀ i j at hpole
    rw [← hpole]
    exact hmul
  have hneg := eventually_negDef_of_entrywise_tendsto G G₀ hG₀neg hconv
  have hupper := eventually_poleApproachNode_upper t ht
  have hregular := eventually_suzukiCanonicalE_ne_zero_poleApproach omega t htinj
  have hall : ∀ᶠ y : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∀ i, 0 < (poleApproachNode t y i).im) ∧
      (∀ i, suzukiCanonicalE omega (poleApproachNode t y i) ≠ 0) ∧
      (∀ c : Fin r → ℂ, c ≠ 0 →
        (star c ⬝ᵥ (G y).mulVec c).re < 0) := by
    filter_upwards [hupper, hregular, hneg] with y hyupper hyregular hyneg
    exact ⟨hyupper, hyregular, hyneg⟩
  obtain ⟨y, hyupper, hyregular, hyneg⟩ := hall.exists
  let w : Fin r → XiShiftRegularUpperNode omega := fun i =>
    ⟨poleApproachNode t y i, hyupper i, hyregular i⟩
  let Kclear : XiShiftRegularUpperNode omega →
      XiShiftRegularUpperNode omega → ℂ := fun z v =>
    xiShiftClearedUpperKernel omega z.1 v.1
  let Kpacket : Fin r → Fin r → ℂ := fun i j =>
    a i * Kclear (w i) (w j) * (starRingEnd ℂ) (a j)
  have hpacketNeg : HasFiniteKernelNegativeDimension Kpacket r := by
    apply hasFiniteKernelNegativeDimension_of_sampleTranspose_negDef
      Kpacket (fun i => i)
    intro c hc
    have hmatrix : (Matrix.of fun i j =>
        Kpacket ((fun k : Fin r => k) j) ((fun k : Fin r => k) i)) = G y := by
      ext i j
      rfl
    rw [hmatrix]
    exact hyneg c hc
  have hclearNeg : HasFiniteKernelNegativeDimension Kclear r := by
    apply hasFiniteKernelNegativeDimension_of_diagonal_pullback
      Kpacket Kclear w a ha
    · intro i j
      rfl
    · exact hpacketNeg
  apply hasFiniteKernelNegativeDimension_of_diagonal_pullback
    Kclear (xiShiftRegularUpperKernel omega) (fun z => z)
      (fun z => suzukiCanonicalE omega z.1)
      (fun z => z.property.2)
  · intro z v
    exact xiShiftClearedUpperKernel_eq_regular_congruence omega z v
  · exact hclearNeg

/-- Exact finite-or-infinite negative-index classification for every nonexceptional positive
shift. In the finite branch the index is the total strict-right divisor-copy cardinality; in the
infinite branch finite negative dimensions are unbounded. -/
theorem xiShiftRegularUpperKernel_negativeIndex_classification
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega) :
    (Finite (XiShiftRightZeroCopy omega) ∧
      HasFiniteKernelNegativeDimension
        (xiShiftRegularUpperKernel omega)
        (Nat.card (XiShiftRightZeroCopy omega)) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
          (xiShiftRegularUpperKernel omega) r →
        r ≤ Nat.card (XiShiftRightZeroCopy omega)) ∨
    (Infinite (XiShiftRightZeroCopy omega) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
        (xiShiftRegularUpperKernel omega) r) := by
  rcases finite_or_infinite (XiShiftRightZeroCopy omega) with hfinite | hinfinite
  · left
    letI : Finite (XiShiftRightZeroCopy omega) := hfinite
    letI : Fintype (XiShiftRightZeroCopy omega) :=
      Fintype.ofFinite (XiShiftRightZeroCopy omega)
    have hfiniteIndex :=
      xiShiftRegularUpperKernel_exactNegativeSquares_finite homega.le hnon
    refine ⟨hfinite, ?_, ?_⟩
    · rw [Nat.card_eq_fintype_card]
      exact hfiniteIndex.1
    · intro r hr
      rw [Nat.card_eq_fintype_card]
      exact hfiniteIndex.2 r hr
  · right
    letI : Infinite (XiShiftRightZeroCopy omega) := hinfinite
    exact ⟨hinfinite,
      xiShiftRegularUpperKernel_hasNegativeDimension_infinite hnon⟩

end

end RHTower
