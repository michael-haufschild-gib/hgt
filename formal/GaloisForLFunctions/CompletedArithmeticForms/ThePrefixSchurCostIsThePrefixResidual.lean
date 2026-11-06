import GaloisForLFunctions.CompletedArithmeticForms.WeilPrefixPayment
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileIsPositiveAtLogLogOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilFormIsPositiveAtEveryFixedOverlap

/-!
# The prefix Schur cost is the prefix residual

Split the complete Weil matrix on `[1,N]` as prefix `A` on `[1,M]`, mixed block `B`, tail `D`. The
Schur cost at the tail of a vector `z` is not `(By)ᵀA⁻¹(By)` in isolation: completing the square gives
the exact identity

`(tail z)ᵀ(D − BᵀA⁻¹B)(tail z) = zᵀWz − rᵀA⁻¹r`,  `r = (Wz)|_{[1,M]}`,

so the whole debit is the residual of `z` on the prefix. For the plateau, `A⁻¹ ≤ 20`.

The crude bound `20‖By‖²` is too large: `By = r − Ap` contains the term `Ap`, of size `log N` on a
fixed prefix, while the true cost stays bounded. In the residual form a conductor vector costs almost
nothing, because it is nearly an eigenvector. Hence the Schur complement inherits the conductor floor on
every fixed block (`exists_plateauPrefixSchur_floor_on_conductor_block`).
-/

noncomputable section

open Matrix Finset Filter Topology MeasureTheory
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open TransMetzlerWeilPositivity SpacingScaleHarmonicAnalysis
  CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The prefix coordinates of a vector. -/
def prefixPart {M N : ℕ} (hMN : M ≤ N) (x : PrimeHorizonIndex N → ℝ) : PrimeHorizonIndex M → ℝ :=
  fun n => x (horizonPrefixMap hMN n)

/-- The tail coordinates of a vector. -/
def tailPart {M N : ℕ} (x : PrimeHorizonIndex N → ℝ) : HorizonTail M N → ℝ :=
  fun n => x n.val

private theorem adjoint_pair {I J : Type*} [Fintype I] [Fintype J]
    (B : Matrix I J ℝ) (y : J → ℝ) (z : I → ℝ) :
    y ⬝ᵥ Bᴴ *ᵥ z = (B *ᵥ y) ⬝ᵥ z := by
  simp only [dotProduct, Matrix.mulVec, conjTranspose_apply, star_trivial,
    Finset.mul_sum, Finset.sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

/-- Block expansion of the complete action on the prefix coordinates. -/
theorem prefixPart_mulVec {M N : ℕ} (hMN : M ≤ N) (c : ℝ) (x : PrimeHorizonIndex N → ℝ) :
    prefixPart hMN (completeWeilMatrix transMetzlerProfile c N *ᵥ x) =
      plateauPrefixBlock hMN c *ᵥ prefixPart hMN x + plateauMixedBlock hMN c *ᵥ tailPart x := by
  have hblocks := completeWeilMatrix_prefix_blocks hMN c
  have hz : x ∘ horizonPrefixSplit hMN = Sum.elim (prefixPart hMN x) (tailPart x) := by
    funext i
    cases i <;> rfl
  funext j
  have h := congrFun (Matrix.submatrix_mulVec_equiv (completeWeilMatrix transMetzlerProfile c N)
    (x ∘ horizonPrefixSplit hMN) (horizonPrefixSplit hMN) (horizonPrefixSplit hMN)) (Sum.inl j)
  rw [hblocks, hz, Matrix.fromBlocks_mulVec] at h
  have hsymm : (Sum.elim (prefixPart hMN x) (tailPart x)) ∘ (horizonPrefixSplit hMN).symm = x := by
    rw [← hz]
    funext i
    simp
  rw [hsymm] at h
  exact h.symm

/-- Block expansion of the complete quadratic form. -/
theorem quadratic_prefix_split {M N : ℕ} (hMN : M ≤ N) (c : ℝ) (x : PrimeHorizonIndex N → ℝ) :
    x ⬝ᵥ completeWeilMatrix transMetzlerProfile c N *ᵥ x =
      prefixPart hMN x ⬝ᵥ plateauPrefixBlock hMN c *ᵥ prefixPart hMN x +
        2 * (prefixPart hMN x ⬝ᵥ plateauMixedBlock hMN c *ᵥ tailPart x) +
          tailPart x ⬝ᵥ plateauTailBlock M N c *ᵥ tailPart x := by
  have hblocks := completeWeilMatrix_prefix_blocks hMN c
  have hz : x ∘ horizonPrefixSplit hMN = Sum.elim (prefixPart hMN x) (tailPart x) := by
    funext i
    cases i <;> rfl
  have hsymm : (x ∘ horizonPrefixSplit hMN) ∘ (horizonPrefixSplit hMN).symm = x := by
    funext i
    simp
  have h1 : x ⬝ᵥ completeWeilMatrix transMetzlerProfile c N *ᵥ x =
      (x ∘ horizonPrefixSplit hMN) ⬝ᵥ
        ((completeWeilMatrix transMetzlerProfile c N).submatrix
          (horizonPrefixSplit hMN) (horizonPrefixSplit hMN) *ᵥ (x ∘ horizonPrefixSplit hMN)) := by
    rw [Matrix.submatrix_mulVec_equiv, hsymm]
    exact (Equiv.sum_comp (horizonPrefixSplit hMN) fun j =>
      x j * (completeWeilMatrix transMetzlerProfile c N *ᵥ x) j).symm
  rw [h1, hblocks, hz, Matrix.fromBlocks_mulVec]
  have hinl : Sum.elim (prefixPart hMN x) (tailPart (M := M) x) ∘ Sum.inl = prefixPart hMN x := rfl
  have hinr : Sum.elim (prefixPart hMN x) (tailPart (M := M) x) ∘ Sum.inr = tailPart (M := M) x := rfl
  have helim : ∀ (a u : PrimeHorizonIndex M → ℝ) (b v : HorizonTail M N → ℝ),
      Sum.elim a b ⬝ᵥ Sum.elim u v = a ⬝ᵥ u + b ⬝ᵥ v := fun a u b v => by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [hinl, hinr, helim, dotProduct_add, dotProduct_add,
    adjoint_pair, dotProduct_comm (plateauMixedBlock hMN c *ᵥ tailPart x) (prefixPart hMN x)]
  ring

/-- **The exact Schur cost.** The Schur form at the tail of `x` is the complete form at `x` minus the
inverse prefix form at the prefix residual of `x`. -/
theorem prefixSchur_tail_eq {M N : ℕ} (hMN : M ≤ N) {c : ℝ}
    (hA : (plateauPrefixBlock hMN c).PosDef) (x : PrimeHorizonIndex N → ℝ) :
    tailPart x ⬝ᵥ plateauPrefixSchur hMN c *ᵥ tailPart x =
      x ⬝ᵥ completeWeilMatrix transMetzlerProfile c N *ᵥ x -
        prefixPart hMN (completeWeilMatrix transMetzlerProfile c N *ᵥ x) ⬝ᵥ
          (plateauPrefixBlock hMN c)⁻¹ *ᵥ
            prefixPart hMN (completeWeilMatrix transMetzlerProfile c N *ᵥ x) := by
  obtain ⟨A, hAd⟩ : ∃ A, A = plateauPrefixBlock hMN c := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = plateauMixedBlock hMN c := ⟨_, rfl⟩
  obtain ⟨p, hpd⟩ : ∃ p, p = prefixPart hMN x := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y, y = tailPart (M := M) x := ⟨_, rfl⟩
  have hunit : IsUnit A.det := by
    rw [hAd]
    exact isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hAinv : A⁻¹ *ᵥ (A *ᵥ p) = p := by
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul A hunit, one_mulVec]
  have hAsymm : ∀ u v : PrimeHorizonIndex M → ℝ, u ⬝ᵥ A *ᵥ v = (A *ᵥ u) ⬝ᵥ v := by
    intro u v
    have hH : A.IsHermitian := by rw [hAd]; exact hA.isHermitian
    have h := adjoint_pair A u v
    rw [hH.eq] at h
    exact h
  have hAinvsymm : ∀ u v : PrimeHorizonIndex M → ℝ, u ⬝ᵥ A⁻¹ *ᵥ v = (A⁻¹ *ᵥ u) ⬝ᵥ v := by
    intro u v
    have hH : A⁻¹.IsHermitian := by
      have hH' : A.IsHermitian := by rw [hAd]; exact hA.isHermitian
      exact hH'.inv
    have h := adjoint_pair A⁻¹ u v
    rw [hH.eq] at h
    exact h
  have hquad := quadratic_prefix_split hMN c x
  have hres := prefixPart_mulVec hMN c x
  rw [← hAd, ← hBd, ← hpd, ← hyd] at hquad hres
  have hS : y ⬝ᵥ plateauPrefixSchur hMN c *ᵥ y =
      y ⬝ᵥ plateauTailBlock M N c *ᵥ y - (B *ᵥ y) ⬝ᵥ A⁻¹ *ᵥ (B *ᵥ y) := by
    rw [plateauPrefixSchur, sub_mulVec, dotProduct_sub, ← hAd, ← hBd,
      ← mulVec_mulVec, ← mulVec_mulVec, adjoint_pair]
  rw [← hyd, hS, hres, hquad, ← hAd]
  -- Complete the square in the inverse prefix form.
  have e1 : (A *ᵥ p + B *ᵥ y) ⬝ᵥ A⁻¹ *ᵥ (A *ᵥ p + B *ᵥ y) =
      p ⬝ᵥ A *ᵥ p + 2 * (p ⬝ᵥ B *ᵥ y) + (B *ᵥ y) ⬝ᵥ A⁻¹ *ᵥ (B *ᵥ y) := by
    rw [mulVec_add, hAinv, add_dotProduct, dotProduct_add, dotProduct_add]
    have h1 : (A *ᵥ p) ⬝ᵥ A⁻¹ *ᵥ (B *ᵥ y) = p ⬝ᵥ B *ᵥ y := by
      rw [hAinvsymm, hAinv]
    have h2 : (B *ᵥ y) ⬝ᵥ p = p ⬝ᵥ B *ᵥ y := dotProduct_comm _ _
    have h3 : (A *ᵥ p) ⬝ᵥ p = p ⬝ᵥ A *ᵥ p := dotProduct_comm _ _
    rw [h1, h2, h3]
    ring
  rw [e1]
  ring

/-- The complete action on a conductor combination, coordinate by coordinate. -/
private theorem completeWeil_mulVec_sum (c : ℝ) {Q N : ℕ} (a : ℕ → ℝ) (i : PrimeHorizonIndex N) :
    (completeWeilMatrix transMetzlerProfile c N *ᵥ
        (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N).ofLp) i =
      ∑ m ∈ Icc 1 Q, a m * (completeWeilMatrix transMetzlerProfile c N *ᵥ
        (normalizedRamanujanHorizonVector m N).ofLp) i := by
  have he : (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N).ofLp =
      ∑ m ∈ Icc 1 Q, a m • (normalizedRamanujanHorizonVector m N).ofLp := by
    funext j
    simp [Finset.sum_apply]
  rw [he, Matrix.mulVec_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]

/-- **The Schur complement keeps the conductor floor on fixed blocks.** There is one prefix length
above which, at every fixed overlap `c ≥ 1` and conductor bound `Q`, the plateau Schur complement is
coercive on the tails of the conductor subspace, once `N` is large. -/
theorem exists_plateauPrefixSchur_floor_on_conductor_block :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∀ c : ℝ, 1 ≤ c → ∀ Q : ℕ, ∃ e : ℝ, 0 < e ∧
      ∀ᶠ N : ℕ in atTop, ∀ hMN : M ≤ N, ∀ z ∈ conductorSubspace Q N,
        e * ‖z‖ ^ 2 ≤ tailPart z.ofLp ⬝ᵥ plateauPrefixSchur hMN c *ᵥ tailPart z.ofLp := by
  have hφ := contDiff_transMetzlerProfile
  have hsupp : ∀ x, x ∉ Set.Icc (0 : ℝ) 1 → transMetzlerProfile x = 0 :=
    fun _ hx => transMetzlerProfile_eq_zero hx
  have hmass := integral_transMetzlerProfile_sq_pos
  obtain ⟨B, hB, hfloorAll⟩ := exists_universal_loglog_overlap_coercivity
  obtain ⟨a₀, ha₀, hfloor⟩ := hfloorAll transMetzlerProfile hφ hsupp hmass
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    (eventually_plateauPrefixBlock_posDef.and eventually_plateauPrefix_inverse_quadratic_le)
  refine ⟨M₀, fun M hM c hc Q => ?_⟩
  obtain ⟨hApos, hAinv⟩ := hM₀ M hM
  have hc0 : 0 < c := by linarith only [hc]
  obtain ⟨e₀, he₀⟩ : ∃ e₀, e₀ = a₀ * Real.exp (-B * c) := ⟨_, rfl⟩
  have he₀0 : 0 < e₀ := by rw [he₀]; positivity
  refine ⟨e₀ / 2, by positivity, ?_⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q', Q' = max Q 2 := ⟨_, rfl⟩
  have hQQ' : Q ≤ Q' := by rw [hQ']; exact le_max_left _ _
  have hQ'2 : 2 ≤ Q' := by rw [hQ']; exact le_max_right _ _
  -- The small quantity on the prefix.
  let E : ℕ → ℝ := completedConductorEnergy transMetzlerProfile c
  let C : ℕ → ℝ := fun m => ∑ j : PrimeHorizonIndex M, ramanujanPoleProfile m j ^ 2
  let resid : ℕ → ℕ → ℝ := fun m N =>
    ‖Matrix.toEuclideanLin (completeWeilMatrix transMetzlerProfile c N)
        (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy transMetzlerProfile c m • normalizedRamanujanHorizonVector m N‖
  let H : ℕ → ℝ := fun N => ∑ m ∈ Icc 1 Q',
    (2 * E m ^ 2 * (C m * (Real.log N)⁻¹) + 2 * resid m N ^ 2)
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hHlim : Tendsto H atTop (𝓝 0) := by
    have hterm : ∀ m ∈ Icc 1 Q', Tendsto (fun N : ℕ =>
        2 * E m ^ 2 * (C m * (Real.log N)⁻¹) + 2 * resid m N ^ 2) atTop (𝓝 0) := by
      intro m hm
      have hm0 : 0 < m := (mem_Icc.mp hm).1
      have h1 : Tendsto (fun N : ℕ => 2 * E m ^ 2 * (C m * (Real.log N)⁻¹)) atTop (𝓝 0) := by
        simpa only [mul_zero, Pi.inv_apply] using
          (hLlim.inv_tendsto_atTop.const_mul (C m)).const_mul (2 * E m ^ 2)
      have h2 : Tendsto (fun N : ℕ => 2 * resid m N ^ 2) atTop (𝓝 0) := by
        have h := (tendsto_completeWeilMatrix_completedConductor_residual_norm hφ hsupp hmass hc0
          hm0).pow 2
        simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] using
          h.const_mul 2
      simpa only [add_zero] using h1.add h2
    have := tendsto_finsetSum (Icc 1 Q') hterm
    simpa only [Finset.sum_const_zero] using this
  have hα : 2 * B * (1 / (4 * B)) < 1 := by
    have : 2 * B * (1 / (4 * B)) = 1 / 2 := by field_simp; norm_num
    rw [this]
    norm_num
  have hevfloor := hfloor (1 / 4) (by norm_num) (by norm_num) (1 / (4 * B)) (by positivity) hα
  have hloglog : Tendsto (fun N : ℕ => 1 / (4 * B) * Real.log (Real.log (N : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp hLlim).const_mul_atTop (by positivity)
  have hrpow : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hLlim
  filter_upwards [hevfloor, hHlim.eventually (gt_mem_nhds (show 0 < e₀ / 80 by positivity)),
    hloglog.eventually_ge_atTop c, hrpow.eventually_ge_atTop ((Q' : ℝ) + 1),
    hLlim.eventually_ge_atTop (4 * Real.log Q' + 18), eventually_ge_atTop (Q' * Q'),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (c * M)] with
    N hN hHN hcN hQN hlogN hQQN hcMN
  intro hMN z hz
  have hL0 : 0 < Real.log (N : ℝ) := by
    have h0 : 0 ≤ Real.log (Q' : ℝ) := Real.log_natCast_nonneg _
    linarith only [hlogN, h0]
  -- The coercive conductor floor.
  have hQfloor : Q' ≤ ⌊Real.log (N : ℝ) ^ (1 / 4 : ℝ)⌋₊ := by
    apply Nat.le_floor
    linarith only [hQN]
  have hzQ' : z ∈ conductorSubspace Q' N := conductorSubspace_mono hQQ' N hz
  have hfl := hN c hc hcN z (conductorSubspace_mono hQfloor N hzQ')
  rw [← he₀] at hfl
  have henergy : completeWeilEnergy transMetzlerProfile c N z =
      z.ofLp ⬝ᵥ completeWeilMatrix transMetzlerProfile c N *ᵥ z.ofLp := by
    unfold completeWeilEnergy
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, star_trivial]
  rw [henergy] at hfl
  -- The exact Schur identity and the inverse bound.
  have hA := hApos N hMN c hc0 hcMN
  rw [prefixSchur_tail_eq hMN hA z.ofLp]
  obtain ⟨r, hrd⟩ : ∃ r, r = prefixPart hMN (completeWeilMatrix transMetzlerProfile c N *ᵥ z.ofLp) :=
    ⟨_, rfl⟩
  rw [← hrd]
  have hinv := (hAinv N hMN c hc0 hcMN r).2
  -- The residual of a conductor vector on the prefix.
  obtain ⟨a, -, hza⟩ := (mem_conductorSubspace_iff (M := Q') (N := N) (x := z)).mp hzQ'
  have hriesz := (half_and_three_halves_riesz_of_four_log_le hQ'2 hQQN hlogN a).1
  rw [← hza] at hriesz
  have hrr : r ⬝ᵥ r ≤ (∑ m ∈ Icc 1 Q', a m ^ 2) * H N := by
    have hcoord : ∀ j : PrimeHorizonIndex M, r j = ∑ m ∈ Icc 1 Q', a m *
        (completeWeilMatrix transMetzlerProfile c N *ᵥ
          (normalizedRamanujanHorizonVector m N).ofLp) (horizonPrefixMap hMN j) := by
      intro j
      rw [hrd, hza]
      exact completeWeil_mulVec_sum c a _
    have hrow : ∀ m ∈ Icc 1 Q', ∑ j : PrimeHorizonIndex M,
        ((completeWeilMatrix transMetzlerProfile c N *ᵥ
          (normalizedRamanujanHorizonVector m N).ofLp) (horizonPrefixMap hMN j)) ^ 2 ≤
        2 * E m ^ 2 * (C m * (Real.log N)⁻¹) + 2 * resid m N ^ 2 := by
      intro m _
      obtain ⟨res, hres⟩ : ∃ res, res = Matrix.toEuclideanLin
          (completeWeilMatrix transMetzlerProfile c N) (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy transMetzlerProfile c m •
              normalizedRamanujanHorizonVector m N := ⟨_, rfl⟩
      have hpt : ∀ i : PrimeHorizonIndex N,
          (completeWeilMatrix transMetzlerProfile c N *ᵥ
            (normalizedRamanujanHorizonVector m N).ofLp) i =
            E m * (normalizedRamanujanHorizonVector m N).ofLp i + res.ofLp i := by
        intro i
        have h := congrArg (fun v : EuclideanSpace ℝ (PrimeHorizonIndex N) => v.ofLp i) hres
        simp only [Matrix.toLpLin_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h
        simp only [E]
        linarith only [h]
      have hvec : ∀ j : PrimeHorizonIndex M,
          ((normalizedRamanujanHorizonVector m N).ofLp (horizonPrefixMap hMN j)) ^ 2 =
            ramanujanPoleProfile m j ^ 2 * (Real.log N)⁻¹ := by
        intro j
        have h1 : (normalizedRamanujanHorizonVector m N).ofLp (horizonPrefixMap hMN j) =
            (Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m j := by
          simp [normalizedRamanujanHorizonVector, ramanujanHorizonVector, horizonPrefixMap]
        rw [h1, mul_pow, inv_pow, Real.sq_sqrt hL0.le]
        ring
      have hresn : ∑ j : PrimeHorizonIndex M, (res.ofLp (horizonPrefixMap hMN j)) ^ 2 ≤
          resid m N ^ 2 := by
        have hnorm : resid m N ^ 2 = ∑ i : PrimeHorizonIndex N, (res.ofLp i) ^ 2 := by
          simp only [resid]
          rw [← hres, EuclideanSpace.real_norm_sq_eq]
        rw [hnorm]
        have hinj : Function.Injective (horizonPrefixMap hMN) := fun i j h => by
          have hv : (horizonPrefixMap hMN i).val = (horizonPrefixMap hMN j).val := congrArg _ h
          exact Subtype.ext hv
        rw [← Finset.sum_image (f := fun i => (res.ofLp i) ^ 2)
          (s := (Finset.univ : Finset (PrimeHorizonIndex M))) (g := horizonPrefixMap hMN)
          (fun i _ j _ h => hinj h)]
        exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
      calc ∑ j : PrimeHorizonIndex M, ((completeWeilMatrix transMetzlerProfile c N *ᵥ
              (normalizedRamanujanHorizonVector m N).ofLp) (horizonPrefixMap hMN j)) ^ 2
          ≤ ∑ j : PrimeHorizonIndex M, (2 * E m ^ 2 *
              ((normalizedRamanujanHorizonVector m N).ofLp (horizonPrefixMap hMN j)) ^ 2 +
              2 * (res.ofLp (horizonPrefixMap hMN j)) ^ 2) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [hpt]
            nlinarith only [sq_nonneg (E m * (normalizedRamanujanHorizonVector m N).ofLp
              (horizonPrefixMap hMN j) - res.ofLp (horizonPrefixMap hMN j))]
        _ = 2 * E m ^ 2 * (C m * (Real.log N)⁻¹) +
              2 * ∑ j : PrimeHorizonIndex M, (res.ofLp (horizonPrefixMap hMN j)) ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            congr 2
            simp only [hvec, C, Finset.sum_mul]
        _ ≤ _ := by linarith only [hresn]
    have hdot : r ⬝ᵥ r = ∑ j : PrimeHorizonIndex M, r j ^ 2 := by
      simp only [dotProduct, sq]
    rw [hdot]
    calc ∑ j : PrimeHorizonIndex M, r j ^ 2
        ≤ ∑ j : PrimeHorizonIndex M, ((∑ m ∈ Icc 1 Q', a m ^ 2) *
            ∑ m ∈ Icc 1 Q', ((completeWeilMatrix transMetzlerProfile c N *ᵥ
              (normalizedRamanujanHorizonVector m N).ofLp) (horizonPrefixMap hMN j)) ^ 2) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hcoord]
          exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ m ∈ Icc 1 Q', a m ^ 2) * ∑ m ∈ Icc 1 Q', ∑ j : PrimeHorizonIndex M,
            ((completeWeilMatrix transMetzlerProfile c N *ᵥ
              (normalizedRamanujanHorizonVector m N).ofLp) (horizonPrefixMap hMN j)) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hA2 : ∑ m ∈ Icc 1 Q', a m ^ 2 ≤ 2 * ‖z‖ ^ 2 := by linarith only [hriesz]
  have hz2 : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  have hH0 : 0 ≤ H N := by
    refine Finset.sum_nonneg fun m _ => ?_
    have hC0 : 0 ≤ C m := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hLinv : 0 ≤ (Real.log (N : ℝ))⁻¹ := (inv_pos.mpr hL0).le
    positivity
  have hrr2 : r ⬝ᵥ r ≤ 2 * ‖z‖ ^ 2 * (e₀ / 80) :=
    hrr.trans (mul_le_mul hA2 hHN.le hH0 (by positivity))
  have hdebit : r ⬝ᵥ (plateauPrefixBlock hMN c)⁻¹ *ᵥ r ≤ e₀ / 2 * ‖z‖ ^ 2 := by
    refine hinv.trans ?_
    calc 20 * (r ⬝ᵥ r) ≤ 20 * (2 * ‖z‖ ^ 2 * (e₀ / 80)) := by gcongr
      _ = _ := by ring
  linarith only [hfl, hdebit]

end GaloisForLFunctions.CompletedArithmeticForms
