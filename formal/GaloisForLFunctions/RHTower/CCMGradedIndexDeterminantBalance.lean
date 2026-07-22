import GaloisForLFunctions.RHTower.CCMFullCharpolyCentralZeroNoGo

/-!
# CCM graded-index determinant balance

An operator which is odd for a finite `Even ⊕ Odd` grading has block form

`A(e,o) = (B o, C e)`.

Its zero space is exactly `ker C ⊕ ker B`.  Consequently its geometric central multiplicity is
at least the absolute grading imbalance.  This is an index obstruction, independent of
self-adjointness, positivity, displacement rank, or the chosen radical correction.

For the CCM reflection grading, the ambient dimensions are `(N+1,N)`.  After quotienting a
graded radical with dimensions `(rEven,rOdd)`, the reduced dimensions balance exactly when

`rEven = rOdd + 1`.

Therefore locally uniform convergence of scalar-normalized reduced characteristic polynomials to
centered Xi forces this radical parity index eventually.  In the published one-dimensional
radical regime, convergence forces the radical to be even.  Arbitrary boundary-channel
completion thus removes the finite metric-adjointness obstruction, but it cannot remove CCM's
cofinal parity-selection theorem.
-/

noncomputable section

namespace RHTower

open Filter LinearMap Topology

variable {E O : Type*}
  [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
  [AddCommGroup O] [Module ℂ O] [FiniteDimensional ℂ O]

/-- General operator which is odd for the grading `E ⊕ O`. -/
def ccmGradedIndexOperator (B : O →ₗ[ℂ] E) (C : E →ₗ[ℂ] O) :
    E × O →ₗ[ℂ] E × O where
  toFun v := (B v.2, C v.1)
  map_add' v w := by ext <;> simp
  map_smul' a v := by ext <;> simp

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ O] in
@[simp]
theorem ccmGradedIndexOperator_apply
    (B : O →ₗ[ℂ] E) (C : E →ₗ[ℂ] O) (v : E × O) :
    ccmGradedIndexOperator B C v = (B v.2, C v.1) := rfl

/-- The central zero space of an odd graded operator is exactly the product of its two cross-block
kernels. -/
def ccmGradedIndexOperatorKernelEquiv (B : O →ₗ[ℂ] E) (C : E →ₗ[ℂ] O) :
    LinearMap.ker (ccmGradedIndexOperator B C) ≃ₗ[ℂ]
      LinearMap.ker C × LinearMap.ker B where
  toFun v :=
    (⟨v.1.1, by
      have hv := LinearMap.mem_ker.mp v.2
      exact congrArg Prod.snd hv⟩,
     ⟨v.1.2, by
      have hv := LinearMap.mem_ker.mp v.2
      exact congrArg Prod.fst hv⟩)
  invFun v :=
    ⟨(v.1.1, v.2.1), LinearMap.mem_ker.mpr (by
      ext
      · exact v.2.2
      · exact v.1.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact nullity law for every finite odd graded operator. -/
theorem ccmGradedIndexOperator_ker_finrank
    (B : O →ₗ[ℂ] E) (C : E →ₗ[ℂ] O) :
    Module.finrank ℂ (LinearMap.ker (ccmGradedIndexOperator B C)) =
      Module.finrank ℂ (LinearMap.ker C) + Module.finrank ℂ (LinearMap.ker B) := by
  rw [LinearEquiv.finrank_eq (ccmGradedIndexOperatorKernelEquiv B C)]
  exact Module.finrank_prod

/-- The even-over-odd grading imbalance is a lower bound for central geometric multiplicity. -/
theorem ccm_evenImbalance_le_gradedIndexOperator_ker_finrank
    (B : O →ₗ[ℂ] E) (C : E →ₗ[ℂ] O) :
    Module.finrank ℂ E - Module.finrank ℂ O ≤
      Module.finrank ℂ (LinearMap.ker (ccmGradedIndexOperator B C)) := by
  rw [ccmGradedIndexOperator_ker_finrank]
  have hrank := LinearMap.finrank_range_add_finrank_ker C
  have hrange : Module.finrank ℂ (LinearMap.range C) ≤ Module.finrank ℂ O :=
    Submodule.finrank_le _
  omega

/-- The odd-over-even grading imbalance is a lower bound for central geometric multiplicity. -/
theorem ccm_oddImbalance_le_gradedIndexOperator_ker_finrank
    (B : O →ₗ[ℂ] E) (C : E →ₗ[ℂ] O) :
    Module.finrank ℂ O - Module.finrank ℂ E ≤
      Module.finrank ℂ (LinearMap.ker (ccmGradedIndexOperator B C)) := by
  rw [ccmGradedIndexOperator_ker_finrank]
  have hrank := LinearMap.finrank_range_add_finrank_ker B
  have hrange : Module.finrank ℂ (LinearMap.range B) ≤ Module.finrank ℂ E :=
    Submodule.finrank_le _
  omega

/-- More even than odd dimensions force a nontrivial central zero mode. -/
theorem exists_nonzero_kernel_ccmGradedIndexOperator_of_odd_finrank_lt_even
    (B : O →ₗ[ℂ] E) (C : E →ₗ[ℂ] O)
    (hdim : Module.finrank ℂ O < Module.finrank ℂ E) :
    ∃ v : E × O, v ≠ 0 ∧ ccmGradedIndexOperator B C v = 0 := by
  have hker : LinearMap.ker C ≠ ⊥ := C.ker_ne_bot_of_finrank_lt hdim
  have hlt : (⊥ : Submodule ℂ E) < LinearMap.ker C := bot_lt_iff_ne_bot.mpr hker
  obtain ⟨e, heker, heBot⟩ := SetLike.exists_of_lt hlt
  have he : e ≠ 0 := by
    intro he0
    apply heBot
    simp [he0]
  refine ⟨(e, 0), ?_, ?_⟩
  · simpa using he
  · ext <;> simp [ccmGradedIndexOperator, LinearMap.mem_ker.mp heker]

/-- More odd than even dimensions force a nontrivial central zero mode. -/
theorem exists_nonzero_kernel_ccmGradedIndexOperator_of_even_finrank_lt_odd
    (B : O →ₗ[ℂ] E) (C : E →ₗ[ℂ] O)
    (hdim : Module.finrank ℂ E < Module.finrank ℂ O) :
    ∃ v : E × O, v ≠ 0 ∧ ccmGradedIndexOperator B C v = 0 := by
  have hker : LinearMap.ker B ≠ ⊥ := B.ker_ne_bot_of_finrank_lt hdim
  have hlt : (⊥ : Submodule ℂ O) < LinearMap.ker B := bot_lt_iff_ne_bot.mpr hker
  obtain ⟨o, hoker, hoBot⟩ := SetLike.exists_of_lt hlt
  have ho : o ≠ 0 := by
    intro ho0
    apply hoBot
    simp [ho0]
  refine ⟨(0, o), ?_, ?_⟩
  · simpa using ho
  · ext <;> simp [ccmGradedIndexOperator, LinearMap.mem_ker.mp hoker]

/-- Coordinate sector used for cofinal finite CCM quotient families. -/
abbrev CCMFiniteGradedSector (n : ℕ) := Fin n → ℂ

/-- Unequal graded dimensions force the characteristic polynomial to vanish at the centered
origin. -/
theorem ccmGradedIndexOperator_charpoly_eval_zero_of_dim_ne
    {p q : ℕ}
    (B : CCMFiniteGradedSector q →ₗ[ℂ] CCMFiniteGradedSector p)
    (C : CCMFiniteGradedSector p →ₗ[ℂ] CCMFiniteGradedSector q)
    (hpq : p ≠ q) :
    (ccmGradedIndexOperator B C).charpoly.eval 0 = 0 := by
  rcases lt_or_gt_of_ne hpq with hpq | hpq
  · obtain ⟨v, hv, hAv⟩ :=
      exists_nonzero_kernel_ccmGradedIndexOperator_of_even_finrank_lt_odd B C (by
        simpa using hpq)
    exact linearMap_charpoly_eval_zero_of_nontrivial_kernel _ v hv hAv
  · obtain ⟨v, hv, hAv⟩ :=
      exists_nonzero_kernel_ccmGradedIndexOperator_of_odd_finrank_lt_even B C (by
        simpa using hpq)
    exact linearMap_charpoly_eval_zero_of_nontrivial_kernel _ v hv hAv

/-- **Cofinal grading-balance law.** If scalar-normalized characteristic polynomials of finite odd
graded operators converge locally uniformly to centered Xi, the two graded dimensions must be
equal eventually.  No regularity or nonvanishing condition is imposed on the normalizers. -/
theorem eventually_ccmGradedIndex_balanced_of_normalizedCharpoly_tendstoLocallyUniformly_XiC
    {p q : ℕ → ℕ}
    (B : ∀ k, CCMFiniteGradedSector (q k) →ₗ[ℂ] CCMFiniteGradedSector (p k))
    (C : ∀ k, CCMFiniteGradedSector (p k) →ₗ[ℂ] CCMFiniteGradedSector (q k))
    (u : ℕ → ℂ → ℂ)
    (hconv : TendstoLocallyUniformly
      (fun k z => u k z * (ccmGradedIndexOperator (B k) (C k)).charpoly.eval z)
      XiC atTop) :
    ∀ᶠ k in atTop, p k = q k := by
  have hvalue : Tendsto
      (fun k => u k 0 * (ccmGradedIndexOperator (B k) (C k)).charpoly.eval 0)
      atTop (nhds (XiC 0)) :=
    hconv.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ 0)
  have hnonzero : (({0} : Set ℂ)ᶜ) ∈ nhds (XiC 0) :=
    IsOpen.mem_nhds isOpen_compl_singleton (by simpa using XiC_zero_ne)
  filter_upwards [hvalue.eventually hnonzero] with k hk
  by_contra hpq
  have hz := ccmGradedIndexOperator_charpoly_eval_zero_of_dim_ne (B k) (C k) hpq
  exact hk (by simp [hz])

/-- A CCM quotient of ambient grading `(N+1,N)` is balanced exactly when the even radical exceeds
the odd radical by one dimension. -/
theorem ccm_radicalParity_balance_iff
    (N rEven rOdd : ℕ) (hrEven : rEven ≤ N + 1) (hrOdd : rOdd ≤ N) :
    N + 1 - rEven = N - rOdd ↔ rEven = rOdd + 1 := by
  omega

/-- **Cofinal radical-index law.** Determinant convergence to centered Xi forces the reduced CCM
radical to have parity index one eventually. -/
theorem eventually_ccm_radicalParityIndex_one_of_normalizedCharpoly_convergence
    {N rEven rOdd : ℕ → ℕ}
    (hrEven : ∀ k, rEven k ≤ N k + 1) (hrOdd : ∀ k, rOdd k ≤ N k)
    (B : ∀ k, CCMFiniteGradedSector (N k - rOdd k) →ₗ[ℂ]
      CCMFiniteGradedSector (N k + 1 - rEven k))
    (C : ∀ k, CCMFiniteGradedSector (N k + 1 - rEven k) →ₗ[ℂ]
      CCMFiniteGradedSector (N k - rOdd k))
    (u : ℕ → ℂ → ℂ)
    (hconv : TendstoLocallyUniformly
      (fun k z => u k z * (ccmGradedIndexOperator (B k) (C k)).charpoly.eval z)
      XiC atTop) :
    ∀ᶠ k in atTop, rEven k = rOdd k + 1 := by
  have hbalance :=
    eventually_ccmGradedIndex_balanced_of_normalizedCharpoly_tendstoLocallyUniformly_XiC
      B C u hconv
  filter_upwards [hbalance] with k hk
  exact (ccm_radicalParity_balance_iff
    (N k) (rEven k) (rOdd k) (hrEven k) (hrOdd k)).mp hk

/-- For a one-dimensional CCM radical, balanced quotient grading is equivalent to the radical
being entirely even. -/
theorem ccm_oneDimensionalRadical_balance_iff_even
    (N rEven rOdd : ℕ)
    (hrEven : rEven ≤ N + 1) (hrOdd : rOdd ≤ N) (hone : rEven + rOdd = 1) :
    N + 1 - rEven = N - rOdd ↔ rEven = 1 ∧ rOdd = 0 := by
  omega

/-- **Simple-radical parity necessity.** Any cofinal one-dimensional-radical determinant family
converging to centered Xi must select an even radical eventually. -/
theorem eventually_ccm_oneDimensionalRadical_even_of_normalizedCharpoly_convergence
    {N rEven rOdd : ℕ → ℕ}
    (hrEven : ∀ k, rEven k ≤ N k + 1) (hrOdd : ∀ k, rOdd k ≤ N k)
    (hone : ∀ k, rEven k + rOdd k = 1)
    (B : ∀ k, CCMFiniteGradedSector (N k - rOdd k) →ₗ[ℂ]
      CCMFiniteGradedSector (N k + 1 - rEven k))
    (C : ∀ k, CCMFiniteGradedSector (N k + 1 - rEven k) →ₗ[ℂ]
      CCMFiniteGradedSector (N k - rOdd k))
    (u : ℕ → ℂ → ℂ)
    (hconv : TendstoLocallyUniformly
      (fun k z => u k z * (ccmGradedIndexOperator (B k) (C k)).charpoly.eval z)
      XiC atTop) :
    ∀ᶠ k in atTop, rEven k = 1 ∧ rOdd k = 0 := by
  have hbalance :=
    eventually_ccmGradedIndex_balanced_of_normalizedCharpoly_tendstoLocallyUniformly_XiC
      B C u hconv
  filter_upwards [hbalance] with k hk
  exact (ccm_oneDimensionalRadical_balance_iff_even
    (N k) (rEven k) (rOdd k) (hrEven k) (hrOdd k) (hone k)).mp hk

/- **Boundary-activity law.** Suppose the clock maps every even radical vector annihilated by
the even boundary functional into the odd radical, and is injective there.  Radical parity index
one then forces the even boundary functional to be active on the radical.

This is purely finite-dimensional and does not require a one-dimensional radical. -/
omit [FiniteDimensional ℂ E] in
theorem ccm_radicalIndex_one_forces_evenBoundaryActive
    (KEven : Submodule ℂ E) (KOdd : Submodule ℂ O)
    (D : E →ₗ[ℂ] O) (eta : E →ₗ[ℂ] ℂ)
    (htransport : ∀ e : E, e ∈ KEven → eta e = 0 → D e ∈ KOdd)
    (hinjective : ∀ e : E, e ∈ KEven → eta e = 0 → D e = 0 → e = 0)
    (hindex : Module.finrank ℂ KEven = Module.finrank ℂ KOdd + 1) :
    ∃ e : E, e ∈ KEven ∧ eta e ≠ 0 := by
  by_contra hactive
  push Not at hactive
  let J : KEven →ₗ[ℂ] KOdd :=
    { toFun := fun e => ⟨D e.1, htransport e.1 e.2 (hactive e.1 e.2)⟩
      map_add' := by
        intro e f
        ext
        simp
      map_smul' := by
        intro a e
        ext
        simp }
  have hJinj : Function.Injective J := by
    intro e f hef
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hinjective (e.1 - f.1)
    · exact KEven.sub_mem e.2 f.2
    · rw [map_sub, hactive e.1 e.2, hactive f.1 f.2, sub_self]
    · have hzero : J (e - f) = 0 := by rw [map_sub, hef, sub_self]
      exact congrArg Subtype.val hzero
  have hle : Module.finrank ℂ KEven ≤ Module.finrank ℂ KOdd :=
    LinearMap.finrank_le_finrank_of_injective (f := J) hJinj
  omega

/- Displacement-form specialization of `ccm_radicalIndex_one_forces_evenBoundaryActive`.
The rank-one boundary term is the only mechanism by which the even radical can exceed the odd
radical.  If the clock is injective on the boundary kernel, index one forces that term to be
nonzero on an even radical vector. -/
omit [FiniteDimensional ℂ E] in
theorem ccm_displacementRadicalIndex_one_forces_evenBoundaryActive
    (TEven : E →ₗ[ℂ] E) (TOdd : O →ₗ[ℂ] O)
    (D : E →ₗ[ℂ] O) (eta : E →ₗ[ℂ] ℂ) (beta : O)
    (htransport : ∀ e : E, TEven e = 0 →
      TOdd (D e) = -(eta e) • beta)
    (hclock : ∀ e : E, eta e = 0 → D e = 0 → e = 0)
    (hindex : Module.finrank ℂ (LinearMap.ker TEven) =
      Module.finrank ℂ (LinearMap.ker TOdd) + 1) :
    ∃ e : E, TEven e = 0 ∧ eta e ≠ 0 := by
  simpa only [LinearMap.mem_ker] using
    ccm_radicalIndex_one_forces_evenBoundaryActive
      (LinearMap.ker TEven) (LinearMap.ker TOdd) D eta
      (fun e he heta => by
        rw [LinearMap.mem_ker]
        rw [htransport e (LinearMap.mem_ker.mp he), heta]
        simp)
      (fun e _ heta hDe => hclock e heta hDe)
      hindex

/-- **Cofinal active-even selection theorem.** For a CCM displacement family whose scalar-normalized
reduced characteristic polynomials converge locally uniformly to centered Xi, radical parity
index one is forced eventually.  The displacement law and clock injectivity then force the even
boundary functional to be active on the radical eventually.  Hence odd-active and boundary-neutral
completions cannot be divisor-faithful cofinally. -/
theorem eventually_ccm_evenBoundaryActive_of_normalizedCharpoly_convergence
    {N rEven rOdd : ℕ → ℕ}
    (hrEven : ∀ k, rEven k ≤ N k + 1) (hrOdd : ∀ k, rOdd k ≤ N k)
    (B : ∀ k, CCMFiniteGradedSector (N k - rOdd k) →ₗ[ℂ]
      CCMFiniteGradedSector (N k + 1 - rEven k))
    (C : ∀ k, CCMFiniteGradedSector (N k + 1 - rEven k) →ₗ[ℂ]
      CCMFiniteGradedSector (N k - rOdd k))
    (u : ℕ → ℂ → ℂ)
    (hconv : TendstoLocallyUniformly
      (fun k z => u k z * (ccmGradedIndexOperator (B k) (C k)).charpoly.eval z)
      XiC atTop)
    (E O : ℕ → Type*)
    [eadd : ∀ k, AddCommGroup (E k)] [emod : ∀ k, Module ℂ (E k)]
    [oadd : ∀ k, AddCommGroup (O k)] [omod : ∀ k, Module ℂ (O k)]
    [ofin : ∀ k, FiniteDimensional ℂ (O k)]
    (TEven : ∀ k, E k →ₗ[ℂ] E k) (TOdd : ∀ k, O k →ₗ[ℂ] O k)
    (hfinEven : ∀ k, Module.finrank ℂ (LinearMap.ker (TEven k)) = rEven k)
    (hfinOdd : ∀ k, Module.finrank ℂ (LinearMap.ker (TOdd k)) = rOdd k)
    (D : ∀ k, E k →ₗ[ℂ] O k) (eta : ∀ k, E k →ₗ[ℂ] ℂ) (beta : ∀ k, O k)
    (htransport : ∀ k e, TEven k e = 0 →
      TOdd k (D k e) = -(eta k e) • beta k)
    (hclock : ∀ k e, eta k e = 0 → D k e = 0 → e = 0) :
    ∀ᶠ k in atTop, ∃ e : E k, TEven k e = 0 ∧ eta k e ≠ 0 := by
  have hindex :=
    eventually_ccm_radicalParityIndex_one_of_normalizedCharpoly_convergence
      hrEven hrOdd B C u hconv
  filter_upwards [hindex] with k hk
  apply ccm_displacementRadicalIndex_one_forces_evenBoundaryActive
    (TEven k) (TOdd k) (D k) (eta k) (beta k) (htransport k) (hclock k)
  rw [hfinEven k, hfinOdd k]
  exact hk

end RHTower
